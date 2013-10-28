
/** vim: et:ts=4:sw=4:sts=4
 * @license RequireJS 2.1.8 Copyright (c) 2010-2012, The Dojo Foundation All Rights Reserved.
 * Available via the MIT or new BSD license.
 * see: http://github.com/jrburke/requirejs for details
 */
//Not using strict: uneven strict support in browsers, #392, and causes
//problems with requirejs.exec()/transpiler plugins that may not be strict.
/*jslint regexp: true, nomen: true, sloppy: true */
/*global window, navigator, document, importScripts, setTimeout, opera */

var requirejs, require, define;
(function (global) {
    var req, s, head, baseElement, dataMain, src,
        interactiveScript, currentlyAddingScript, mainScript, subPath,
        version = '2.1.8',
        commentRegExp = /(\/\*([\s\S]*?)\*\/|([^:]|^)\/\/(.*)$)/mg,
        cjsRequireRegExp = /[^.]\s*require\s*\(\s*["']([^'"\s]+)["']\s*\)/g,
        jsSuffixRegExp = /\.js$/,
        currDirRegExp = /^\.\//,
        op = Object.prototype,
        ostring = op.toString,
        hasOwn = op.hasOwnProperty,
        ap = Array.prototype,
        apsp = ap.splice,
        isBrowser = !!(typeof window !== 'undefined' && navigator && window.document),
        isWebWorker = !isBrowser && typeof importScripts !== 'undefined',
        //PS3 indicates loaded and complete, but need to wait for complete
        //specifically. Sequence is 'loading', 'loaded', execution,
        // then 'complete'. The UA check is unfortunate, but not sure how
        //to feature test w/o causing perf issues.
        readyRegExp = isBrowser && navigator.platform === 'PLAYSTATION 3' ?
                      /^complete$/ : /^(complete|loaded)$/,
        defContextName = '_',
        //Oh the tragedy, detecting opera. See the usage of isOpera for reason.
        isOpera = typeof opera !== 'undefined' && opera.toString() === '[object Opera]',
        contexts = {},
        cfg = {},
        globalDefQueue = [],
        useInteractive = false;

    function isFunction(it) {
        return ostring.call(it) === '[object Function]';
    }

    function isArray(it) {
        return ostring.call(it) === '[object Array]';
    }

    /**
     * Helper function for iterating over an array. If the func returns
     * a true value, it will break out of the loop.
     */
    function each(ary, func) {
        if (ary) {
            var i;
            for (i = 0; i < ary.length; i += 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    /**
     * Helper function for iterating over an array backwards. If the func
     * returns a true value, it will break out of the loop.
     */
    function eachReverse(ary, func) {
        if (ary) {
            var i;
            for (i = ary.length - 1; i > -1; i -= 1) {
                if (ary[i] && func(ary[i], i, ary)) {
                    break;
                }
            }
        }
    }

    function hasProp(obj, prop) {
        return hasOwn.call(obj, prop);
    }

    function getOwn(obj, prop) {
        return hasProp(obj, prop) && obj[prop];
    }

    /**
     * Cycles over properties in an object and calls a function for each
     * property value. If the function returns a truthy value, then the
     * iteration is stopped.
     */
    function eachProp(obj, func) {
        var prop;
        for (prop in obj) {
            if (hasProp(obj, prop)) {
                if (func(obj[prop], prop)) {
                    break;
                }
            }
        }
    }

    /**
     * Simple function to mix in properties from source into target,
     * but only if target does not already have a property of the same name.
     */
    function mixin(target, source, force, deepStringMixin) {
        if (source) {
            eachProp(source, function (value, prop) {
                if (force || !hasProp(target, prop)) {
                    if (deepStringMixin && typeof value !== 'string') {
                        if (!target[prop]) {
                            target[prop] = {};
                        }
                        mixin(target[prop], value, force, deepStringMixin);
                    } else {
                        target[prop] = value;
                    }
                }
            });
        }
        return target;
    }

    //Similar to Function.prototype.bind, but the 'this' object is specified
    //first, since it is easier to read/figure out what 'this' will be.
    function bind(obj, fn) {
        return function () {
            return fn.apply(obj, arguments);
        };
    }

    function scripts() {
        return document.getElementsByTagName('script');
    }

    function defaultOnError(err) {
        throw err;
    }

    //Allow getting a global that expressed in
    //dot notation, like 'a.b.c'.
    function getGlobal(value) {
        if (!value) {
            return value;
        }
        var g = global;
        each(value.split('.'), function (part) {
            g = g[part];
        });
        return g;
    }

    /**
     * Constructs an error with a pointer to an URL with more information.
     * @param {String} id the error ID that maps to an ID on a web page.
     * @param {String} message human readable error.
     * @param {Error} [err] the original error, if there is one.
     *
     * @returns {Error}
     */
    function makeError(id, msg, err, requireModules) {
        var e = new Error(msg + '\nhttp://requirejs.org/docs/errors.html#' + id);
        e.requireType = id;
        e.requireModules = requireModules;
        if (err) {
            e.originalError = err;
        }
        return e;
    }

    if (typeof define !== 'undefined') {
        //If a define is already in play via another AMD loader,
        //do not overwrite.
        return;
    }

    if (typeof requirejs !== 'undefined') {
        if (isFunction(requirejs)) {
            //Do not overwrite and existing requirejs instance.
            return;
        }
        cfg = requirejs;
        requirejs = undefined;
    }

    //Allow for a require config object
    if (typeof require !== 'undefined' && !isFunction(require)) {
        //assume it is a config object.
        cfg = require;
        require = undefined;
    }

    function newContext(contextName) {
        var inCheckLoaded, Module, context, handlers,
            checkLoadedTimeoutId,
            config = {
                //Defaults. Do not set a default for map
                //config to speed up normalize(), which
                //will run faster if there is no default.
                waitSeconds: 7,
                baseUrl: './',
                paths: {},
                pkgs: {},
                shim: {},
                config: {}
            },
            registry = {},
            //registry of just enabled modules, to speed
            //cycle breaking code when lots of modules
            //are registered, but not activated.
            enabledRegistry = {},
            undefEvents = {},
            defQueue = [],
            defined = {},
            urlFetched = {},
            requireCounter = 1,
            unnormalizedCounter = 1;

        /**
         * Trims the . and .. from an array of path segments.
         * It will keep a leading path segment if a .. will become
         * the first path segment, to help with module name lookups,
         * which act like paths, but can be remapped. But the end result,
         * all paths that use this function should look normalized.
         * NOTE: this method MODIFIES the input array.
         * @param {Array} ary the array of path segments.
         */
        function trimDots(ary) {
            var i, part;
            for (i = 0; ary[i]; i += 1) {
                part = ary[i];
                if (part === '.') {
                    ary.splice(i, 1);
                    i -= 1;
                } else if (part === '..') {
                    if (i === 1 && (ary[2] === '..' || ary[0] === '..')) {
                        //End of the line. Keep at least one non-dot
                        //path segment at the front so it can be mapped
                        //correctly to disk. Otherwise, there is likely
                        //no path mapping for a path starting with '..'.
                        //This can still fail, but catches the most reasonable
                        //uses of ..
                        break;
                    } else if (i > 0) {
                        ary.splice(i - 1, 2);
                        i -= 2;
                    }
                }
            }
        }

        /**
         * Given a relative module name, like ./something, normalize it to
         * a real name that can be mapped to a path.
         * @param {String} name the relative name
         * @param {String} baseName a real name that the name arg is relative
         * to.
         * @param {Boolean} applyMap apply the map config to the value. Should
         * only be done if this normalization is for a dependency ID.
         * @returns {String} normalized name
         */
        function normalize(name, baseName, applyMap) {
            var pkgName, pkgConfig, mapValue, nameParts, i, j, nameSegment,
                foundMap, foundI, foundStarMap, starI,
                baseParts = baseName && baseName.split('/'),
                normalizedBaseParts = baseParts,
                map = config.map,
                starMap = map && map['*'];

            //Adjust any relative paths.
            if (name && name.charAt(0) === '.') {
                //If have a base name, try to normalize against it,
                //otherwise, assume it is a top-level require that will
                //be relative to baseUrl in the end.
                if (baseName) {
                    if (getOwn(config.pkgs, baseName)) {
                        //If the baseName is a package name, then just treat it as one
                        //name to concat the name with.
                        normalizedBaseParts = baseParts = [baseName];
                    } else {
                        //Convert baseName to array, and lop off the last part,
                        //so that . matches that 'directory' and not name of the baseName's
                        //module. For instance, baseName of 'one/two/three', maps to
                        //'one/two/three.js', but we want the directory, 'one/two' for
                        //this normalization.
                        normalizedBaseParts = baseParts.slice(0, baseParts.length - 1);
                    }

                    name = normalizedBaseParts.concat(name.split('/'));
                    trimDots(name);

                    //Some use of packages may use a . path to reference the
                    //'main' module name, so normalize for that.
                    pkgConfig = getOwn(config.pkgs, (pkgName = name[0]));
                    name = name.join('/');
                    if (pkgConfig && name === pkgName + '/' + pkgConfig.main) {
                        name = pkgName;
                    }
                } else if (name.indexOf('./') === 0) {
                    // No baseName, so this is ID is resolved relative
                    // to baseUrl, pull off the leading dot.
                    name = name.substring(2);
                }
            }

            //Apply map config if available.
            if (applyMap && map && (baseParts || starMap)) {
                nameParts = name.split('/');

                for (i = nameParts.length; i > 0; i -= 1) {
                    nameSegment = nameParts.slice(0, i).join('/');

                    if (baseParts) {
                        //Find the longest baseName segment match in the config.
                        //So, do joins on the biggest to smallest lengths of baseParts.
                        for (j = baseParts.length; j > 0; j -= 1) {
                            mapValue = getOwn(map, baseParts.slice(0, j).join('/'));

                            //baseName segment has config, find if it has one for
                            //this name.
                            if (mapValue) {
                                mapValue = getOwn(mapValue, nameSegment);
                                if (mapValue) {
                                    //Match, update name to the new value.
                                    foundMap = mapValue;
                                    foundI = i;
                                    break;
                                }
                            }
                        }
                    }

                    if (foundMap) {
                        break;
                    }

                    //Check for a star map match, but just hold on to it,
                    //if there is a shorter segment match later in a matching
                    //config, then favor over this star map.
                    if (!foundStarMap && starMap && getOwn(starMap, nameSegment)) {
                        foundStarMap = getOwn(starMap, nameSegment);
                        starI = i;
                    }
                }

                if (!foundMap && foundStarMap) {
                    foundMap = foundStarMap;
                    foundI = starI;
                }

                if (foundMap) {
                    nameParts.splice(0, foundI, foundMap);
                    name = nameParts.join('/');
                }
            }

            return name;
        }

        function removeScript(name) {
            if (isBrowser) {
                each(scripts(), function (scriptNode) {
                    if (scriptNode.getAttribute('data-requiremodule') === name &&
                            scriptNode.getAttribute('data-requirecontext') === context.contextName) {
                        scriptNode.parentNode.removeChild(scriptNode);
                        return true;
                    }
                });
            }
        }

        function hasPathFallback(id) {
            var pathConfig = getOwn(config.paths, id);
            if (pathConfig && isArray(pathConfig) && pathConfig.length > 1) {
                removeScript(id);
                //Pop off the first array value, since it failed, and
                //retry
                pathConfig.shift();
                context.require.undef(id);
                context.require([id]);
                return true;
            }
        }

        //Turns a plugin!resource to [plugin, resource]
        //with the plugin being undefined if the name
        //did not have a plugin prefix.
        function splitPrefix(name) {
            var prefix,
                index = name ? name.indexOf('!') : -1;
            if (index > -1) {
                prefix = name.substring(0, index);
                name = name.substring(index + 1, name.length);
            }
            return [prefix, name];
        }

        /**
         * Creates a module mapping that includes plugin prefix, module
         * name, and path. If parentModuleMap is provided it will
         * also normalize the name via require.normalize()
         *
         * @param {String} name the module name
         * @param {String} [parentModuleMap] parent module map
         * for the module name, used to resolve relative names.
         * @param {Boolean} isNormalized: is the ID already normalized.
         * This is true if this call is done for a define() module ID.
         * @param {Boolean} applyMap: apply the map config to the ID.
         * Should only be true if this map is for a dependency.
         *
         * @returns {Object}
         */
        function makeModuleMap(name, parentModuleMap, isNormalized, applyMap) {
            var url, pluginModule, suffix, nameParts,
                prefix = null,
                parentName = parentModuleMap ? parentModuleMap.name : null,
                originalName = name,
                isDefine = true,
                normalizedName = '';

            //If no name, then it means it is a require call, generate an
            //internal name.
            if (!name) {
                isDefine = false;
                name = '_@r' + (requireCounter += 1);
            }

            nameParts = splitPrefix(name);
            prefix = nameParts[0];
            name = nameParts[1];

            if (prefix) {
                prefix = normalize(prefix, parentName, applyMap);
                pluginModule = getOwn(defined, prefix);
            }

            //Account for relative paths if there is a base name.
            if (name) {
                if (prefix) {
                    if (pluginModule && pluginModule.normalize) {
                        //Plugin is loaded, use its normalize method.
                        normalizedName = pluginModule.normalize(name, function (name) {
                            return normalize(name, parentName, applyMap);
                        });
                    } else {
                        normalizedName = normalize(name, parentName, applyMap);
                    }
                } else {
                    //A regular module.
                    normalizedName = normalize(name, parentName, applyMap);

                    //Normalized name may be a plugin ID due to map config
                    //application in normalize. The map config values must
                    //already be normalized, so do not need to redo that part.
                    nameParts = splitPrefix(normalizedName);
                    prefix = nameParts[0];
                    normalizedName = nameParts[1];
                    isNormalized = true;

                    url = context.nameToUrl(normalizedName);
                }
            }

            //If the id is a plugin id that cannot be determined if it needs
            //normalization, stamp it with a unique ID so two matching relative
            //ids that may conflict can be separate.
            suffix = prefix && !pluginModule && !isNormalized ?
                     '_unnormalized' + (unnormalizedCounter += 1) :
                     '';

            return {
                prefix: prefix,
                name: normalizedName,
                parentMap: parentModuleMap,
                unnormalized: !!suffix,
                url: url,
                originalName: originalName,
                isDefine: isDefine,
                id: (prefix ?
                        prefix + '!' + normalizedName :
                        normalizedName) + suffix
            };
        }

        function getModule(depMap) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (!mod) {
                mod = registry[id] = new context.Module(depMap);
            }

            return mod;
        }

        function on(depMap, name, fn) {
            var id = depMap.id,
                mod = getOwn(registry, id);

            if (hasProp(defined, id) &&
                    (!mod || mod.defineEmitComplete)) {
                if (name === 'defined') {
                    fn(defined[id]);
                }
            } else {
                mod = getModule(depMap);
                if (mod.error && name === 'error') {
                    fn(mod.error);
                } else {
                    mod.on(name, fn);
                }
            }
        }

        function onError(err, errback) {
            var ids = err.requireModules,
                notified = false;

            if (errback) {
                errback(err);
            } else {
                each(ids, function (id) {
                    var mod = getOwn(registry, id);
                    if (mod) {
                        //Set error on module, so it skips timeout checks.
                        mod.error = err;
                        if (mod.events.error) {
                            notified = true;
                            mod.emit('error', err);
                        }
                    }
                });

                if (!notified) {
                    req.onError(err);
                }
            }
        }

        /**
         * Internal method to transfer globalQueue items to this context's
         * defQueue.
         */
        function takeGlobalQueue() {
            //Push all the globalDefQueue items into the context's defQueue
            if (globalDefQueue.length) {
                //Array splice in the values since the context code has a
                //local var ref to defQueue, so cannot just reassign the one
                //on context.
                apsp.apply(defQueue,
                           [defQueue.length - 1, 0].concat(globalDefQueue));
                globalDefQueue = [];
            }
        }

        handlers = {
            'require': function (mod) {
                if (mod.require) {
                    return mod.require;
                } else {
                    return (mod.require = context.makeRequire(mod.map));
                }
            },
            'exports': function (mod) {
                mod.usingExports = true;
                if (mod.map.isDefine) {
                    if (mod.exports) {
                        return mod.exports;
                    } else {
                        return (mod.exports = defined[mod.map.id] = {});
                    }
                }
            },
            'module': function (mod) {
                if (mod.module) {
                    return mod.module;
                } else {
                    return (mod.module = {
                        id: mod.map.id,
                        uri: mod.map.url,
                        config: function () {
                            var c,
                                pkg = getOwn(config.pkgs, mod.map.id);
                            // For packages, only support config targeted
                            // at the main module.
                            c = pkg ? getOwn(config.config, mod.map.id + '/' + pkg.main) :
                                      getOwn(config.config, mod.map.id);
                            return  c || {};
                        },
                        exports: defined[mod.map.id]
                    });
                }
            }
        };

        function cleanRegistry(id) {
            //Clean up machinery used for waiting modules.
            delete registry[id];
            delete enabledRegistry[id];
        }

        function breakCycle(mod, traced, processed) {
            var id = mod.map.id;

            if (mod.error) {
                mod.emit('error', mod.error);
            } else {
                traced[id] = true;
                each(mod.depMaps, function (depMap, i) {
                    var depId = depMap.id,
                        dep = getOwn(registry, depId);

                    //Only force things that have not completed
                    //being defined, so still in the registry,
                    //and only if it has not been matched up
                    //in the module already.
                    if (dep && !mod.depMatched[i] && !processed[depId]) {
                        if (getOwn(traced, depId)) {
                            mod.defineDep(i, defined[depId]);
                            mod.check(); //pass false?
                        } else {
                            breakCycle(dep, traced, processed);
                        }
                    }
                });
                processed[id] = true;
            }
        }

        function checkLoaded() {
            var map, modId, err, usingPathFallback,
                waitInterval = config.waitSeconds * 1000,
                //It is possible to disable the wait interval by using waitSeconds of 0.
                expired = waitInterval && (context.startTime + waitInterval) < new Date().getTime(),
                noLoads = [],
                reqCalls = [],
                stillLoading = false,
                needCycleCheck = true;

            //Do not bother if this call was a result of a cycle break.
            if (inCheckLoaded) {
                return;
            }

            inCheckLoaded = true;

            //Figure out the state of all the modules.
            eachProp(enabledRegistry, function (mod) {
                map = mod.map;
                modId = map.id;

                //Skip things that are not enabled or in error state.
                if (!mod.enabled) {
                    return;
                }

                if (!map.isDefine) {
                    reqCalls.push(mod);
                }

                if (!mod.error) {
                    //If the module should be executed, and it has not
                    //been inited and time is up, remember it.
                    if (!mod.inited && expired) {
                        if (hasPathFallback(modId)) {
                            usingPathFallback = true;
                            stillLoading = true;
                        } else {
                            noLoads.push(modId);
                            removeScript(modId);
                        }
                    } else if (!mod.inited && mod.fetched && map.isDefine) {
                        stillLoading = true;
                        if (!map.prefix) {
                            //No reason to keep looking for unfinished
                            //loading. If the only stillLoading is a
                            //plugin resource though, keep going,
                            //because it may be that a plugin resource
                            //is waiting on a non-plugin cycle.
                            return (needCycleCheck = false);
                        }
                    }
                }
            });

            if (expired && noLoads.length) {
                //If wait time expired, throw error of unloaded modules.
                err = makeError('timeout', 'Load timeout for modules: ' + noLoads, null, noLoads);
                err.contextName = context.contextName;
                return onError(err);
            }

            //Not expired, check for a cycle.
            if (needCycleCheck) {
                each(reqCalls, function (mod) {
                    breakCycle(mod, {}, {});
                });
            }

            //If still waiting on loads, and the waiting load is something
            //other than a plugin resource, or there are still outstanding
            //scripts, then just try back later.
            if ((!expired || usingPathFallback) && stillLoading) {
                //Something is still waiting to load. Wait for it, but only
                //if a timeout is not already in effect.
                if ((isBrowser || isWebWorker) && !checkLoadedTimeoutId) {
                    checkLoadedTimeoutId = setTimeout(function () {
                        checkLoadedTimeoutId = 0;
                        checkLoaded();
                    }, 50);
                }
            }

            inCheckLoaded = false;
        }

        Module = function (map) {
            this.events = getOwn(undefEvents, map.id) || {};
            this.map = map;
            this.shim = getOwn(config.shim, map.id);
            this.depExports = [];
            this.depMaps = [];
            this.depMatched = [];
            this.pluginMaps = {};
            this.depCount = 0;

            /* this.exports this.factory
               this.depMaps = [],
               this.enabled, this.fetched
            */
        };

        Module.prototype = {
            init: function (depMaps, factory, errback, options) {
                options = options || {};

                //Do not do more inits if already done. Can happen if there
                //are multiple define calls for the same module. That is not
                //a normal, common case, but it is also not unexpected.
                if (this.inited) {
                    return;
                }

                this.factory = factory;

                if (errback) {
                    //Register for errors on this module.
                    this.on('error', errback);
                } else if (this.events.error) {
                    //If no errback already, but there are error listeners
                    //on this module, set up an errback to pass to the deps.
                    errback = bind(this, function (err) {
                        this.emit('error', err);
                    });
                }

                //Do a copy of the dependency array, so that
                //source inputs are not modified. For example
                //"shim" deps are passed in here directly, and
                //doing a direct modification of the depMaps array
                //would affect that config.
                this.depMaps = depMaps && depMaps.slice(0);

                this.errback = errback;

                //Indicate this module has be initialized
                this.inited = true;

                this.ignore = options.ignore;

                //Could have option to init this module in enabled mode,
                //or could have been previously marked as enabled. However,
                //the dependencies are not known until init is called. So
                //if enabled previously, now trigger dependencies as enabled.
                if (options.enabled || this.enabled) {
                    //Enable this module and dependencies.
                    //Will call this.check()
                    this.enable();
                } else {
                    this.check();
                }
            },

            defineDep: function (i, depExports) {
                //Because of cycles, defined callback for a given
                //export can be called more than once.
                if (!this.depMatched[i]) {
                    this.depMatched[i] = true;
                    this.depCount -= 1;
                    this.depExports[i] = depExports;
                }
            },

            fetch: function () {
                if (this.fetched) {
                    return;
                }
                this.fetched = true;

                context.startTime = (new Date()).getTime();

                var map = this.map;

                //If the manager is for a plugin managed resource,
                //ask the plugin to load it now.
                if (this.shim) {
                    context.makeRequire(this.map, {
                        enableBuildCallback: true
                    })(this.shim.deps || [], bind(this, function () {
                        return map.prefix ? this.callPlugin() : this.load();
                    }));
                } else {
                    //Regular dependency.
                    return map.prefix ? this.callPlugin() : this.load();
                }
            },

            load: function () {
                var url = this.map.url;

                //Regular dependency.
                if (!urlFetched[url]) {
                    urlFetched[url] = true;
                    context.load(this.map.id, url);
                }
            },

            /**
             * Checks if the module is ready to define itself, and if so,
             * define it.
             */
            check: function () {
                if (!this.enabled || this.enabling) {
                    return;
                }

                var err, cjsModule,
                    id = this.map.id,
                    depExports = this.depExports,
                    exports = this.exports,
                    factory = this.factory;

                if (!this.inited) {
                    this.fetch();
                } else if (this.error) {
                    this.emit('error', this.error);
                } else if (!this.defining) {
                    //The factory could trigger another require call
                    //that would result in checking this module to
                    //define itself again. If already in the process
                    //of doing that, skip this work.
                    this.defining = true;

                    if (this.depCount < 1 && !this.defined) {
                        if (isFunction(factory)) {
                            //If there is an error listener, favor passing
                            //to that instead of throwing an error. However,
                            //only do it for define()'d  modules. require
                            //errbacks should not be called for failures in
                            //their callbacks (#699). However if a global
                            //onError is set, use that.
                            if ((this.events.error && this.map.isDefine) ||
                                req.onError !== defaultOnError) {
                                try {
                                    exports = context.execCb(id, factory, depExports, exports);
                                } catch (e) {
                                    err = e;
                                }
                            } else {
                                exports = context.execCb(id, factory, depExports, exports);
                            }

                            if (this.map.isDefine) {
                                //If setting exports via 'module' is in play,
                                //favor that over return value and exports. After that,
                                //favor a non-undefined return value over exports use.
                                cjsModule = this.module;
                                if (cjsModule &&
                                        cjsModule.exports !== undefined &&
                                        //Make sure it is not already the exports value
                                        cjsModule.exports !== this.exports) {
                                    exports = cjsModule.exports;
                                } else if (exports === undefined && this.usingExports) {
                                    //exports already set the defined value.
                                    exports = this.exports;
                                }
                            }

                            if (err) {
                                err.requireMap = this.map;
                                err.requireModules = this.map.isDefine ? [this.map.id] : null;
                                err.requireType = this.map.isDefine ? 'define' : 'require';
                                return onError((this.error = err));
                            }

                        } else {
                            //Just a literal value
                            exports = factory;
                        }

                        this.exports = exports;

                        if (this.map.isDefine && !this.ignore) {
                            defined[id] = exports;

                            if (req.onResourceLoad) {
                                req.onResourceLoad(context, this.map, this.depMaps);
                            }
                        }

                        //Clean up
                        cleanRegistry(id);

                        this.defined = true;
                    }

                    //Finished the define stage. Allow calling check again
                    //to allow define notifications below in the case of a
                    //cycle.
                    this.defining = false;

                    if (this.defined && !this.defineEmitted) {
                        this.defineEmitted = true;
                        this.emit('defined', this.exports);
                        this.defineEmitComplete = true;
                    }

                }
            },

            callPlugin: function () {
                var map = this.map,
                    id = map.id,
                    //Map already normalized the prefix.
                    pluginMap = makeModuleMap(map.prefix);

                //Mark this as a dependency for this plugin, so it
                //can be traced for cycles.
                this.depMaps.push(pluginMap);

                on(pluginMap, 'defined', bind(this, function (plugin) {
                    var load, normalizedMap, normalizedMod,
                        name = this.map.name,
                        parentName = this.map.parentMap ? this.map.parentMap.name : null,
                        localRequire = context.makeRequire(map.parentMap, {
                            enableBuildCallback: true
                        });

                    //If current map is not normalized, wait for that
                    //normalized name to load instead of continuing.
                    if (this.map.unnormalized) {
                        //Normalize the ID if the plugin allows it.
                        if (plugin.normalize) {
                            name = plugin.normalize(name, function (name) {
                                return normalize(name, parentName, true);
                            }) || '';
                        }

                        //prefix and name should already be normalized, no need
                        //for applying map config again either.
                        normalizedMap = makeModuleMap(map.prefix + '!' + name,
                                                      this.map.parentMap);
                        on(normalizedMap,
                            'defined', bind(this, function (value) {
                                this.init([], function () { return value; }, null, {
                                    enabled: true,
                                    ignore: true
                                });
                            }));

                        normalizedMod = getOwn(registry, normalizedMap.id);
                        if (normalizedMod) {
                            //Mark this as a dependency for this plugin, so it
                            //can be traced for cycles.
                            this.depMaps.push(normalizedMap);

                            if (this.events.error) {
                                normalizedMod.on('error', bind(this, function (err) {
                                    this.emit('error', err);
                                }));
                            }
                            normalizedMod.enable();
                        }

                        return;
                    }

                    load = bind(this, function (value) {
                        this.init([], function () { return value; }, null, {
                            enabled: true
                        });
                    });

                    load.error = bind(this, function (err) {
                        this.inited = true;
                        this.error = err;
                        err.requireModules = [id];

                        //Remove temp unnormalized modules for this module,
                        //since they will never be resolved otherwise now.
                        eachProp(registry, function (mod) {
                            if (mod.map.id.indexOf(id + '_unnormalized') === 0) {
                                cleanRegistry(mod.map.id);
                            }
                        });

                        onError(err);
                    });

                    //Allow plugins to load other code without having to know the
                    //context or how to 'complete' the load.
                    load.fromText = bind(this, function (text, textAlt) {
                        /*jslint evil: true */
                        var moduleName = map.name,
                            moduleMap = makeModuleMap(moduleName),
                            hasInteractive = useInteractive;

                        //As of 2.1.0, support just passing the text, to reinforce
                        //fromText only being called once per resource. Still
                        //support old style of passing moduleName but discard
                        //that moduleName in favor of the internal ref.
                        if (textAlt) {
                            text = textAlt;
                        }

                        //Turn off interactive script matching for IE for any define
                        //calls in the text, then turn it back on at the end.
                        if (hasInteractive) {
                            useInteractive = false;
                        }

                        //Prime the system by creating a module instance for
                        //it.
                        getModule(moduleMap);

                        //Transfer any config to this other module.
                        if (hasProp(config.config, id)) {
                            config.config[moduleName] = config.config[id];
                        }

                        try {
                            req.exec(text);
                        } catch (e) {
                            return onError(makeError('fromtexteval',
                                             'fromText eval for ' + id +
                                            ' failed: ' + e,
                                             e,
                                             [id]));
                        }

                        if (hasInteractive) {
                            useInteractive = true;
                        }

                        //Mark this as a dependency for the plugin
                        //resource
                        this.depMaps.push(moduleMap);

                        //Support anonymous modules.
                        context.completeLoad(moduleName);

                        //Bind the value of that module to the value for this
                        //resource ID.
                        localRequire([moduleName], load);
                    });

                    //Use parentName here since the plugin's name is not reliable,
                    //could be some weird string with no path that actually wants to
                    //reference the parentName's path.
                    plugin.load(map.name, localRequire, load, config);
                }));

                context.enable(pluginMap, this);
                this.pluginMaps[pluginMap.id] = pluginMap;
            },

            enable: function () {
                enabledRegistry[this.map.id] = this;
                this.enabled = true;

                //Set flag mentioning that the module is enabling,
                //so that immediate calls to the defined callbacks
                //for dependencies do not trigger inadvertent load
                //with the depCount still being zero.
                this.enabling = true;

                //Enable each dependency
                each(this.depMaps, bind(this, function (depMap, i) {
                    var id, mod, handler;

                    if (typeof depMap === 'string') {
                        //Dependency needs to be converted to a depMap
                        //and wired up to this module.
                        depMap = makeModuleMap(depMap,
                                               (this.map.isDefine ? this.map : this.map.parentMap),
                                               false,
                                               !this.skipMap);
                        this.depMaps[i] = depMap;

                        handler = getOwn(handlers, depMap.id);

                        if (handler) {
                            this.depExports[i] = handler(this);
                            return;
                        }

                        this.depCount += 1;

                        on(depMap, 'defined', bind(this, function (depExports) {
                            this.defineDep(i, depExports);
                            this.check();
                        }));

                        if (this.errback) {
                            on(depMap, 'error', bind(this, this.errback));
                        }
                    }

                    id = depMap.id;
                    mod = registry[id];

                    //Skip special modules like 'require', 'exports', 'module'
                    //Also, don't call enable if it is already enabled,
                    //important in circular dependency cases.
                    if (!hasProp(handlers, id) && mod && !mod.enabled) {
                        context.enable(depMap, this);
                    }
                }));

                //Enable each plugin that is used in
                //a dependency
                eachProp(this.pluginMaps, bind(this, function (pluginMap) {
                    var mod = getOwn(registry, pluginMap.id);
                    if (mod && !mod.enabled) {
                        context.enable(pluginMap, this);
                    }
                }));

                this.enabling = false;

                this.check();
            },

            on: function (name, cb) {
                var cbs = this.events[name];
                if (!cbs) {
                    cbs = this.events[name] = [];
                }
                cbs.push(cb);
            },

            emit: function (name, evt) {
                each(this.events[name], function (cb) {
                    cb(evt);
                });
                if (name === 'error') {
                    //Now that the error handler was triggered, remove
                    //the listeners, since this broken Module instance
                    //can stay around for a while in the registry.
                    delete this.events[name];
                }
            }
        };

        function callGetModule(args) {
            //Skip modules already defined.
            if (!hasProp(defined, args[0])) {
                getModule(makeModuleMap(args[0], null, true)).init(args[1], args[2]);
            }
        }

        function removeListener(node, func, name, ieName) {
            //Favor detachEvent because of IE9
            //issue, see attachEvent/addEventListener comment elsewhere
            //in this file.
            if (node.detachEvent && !isOpera) {
                //Probably IE. If not it will throw an error, which will be
                //useful to know.
                if (ieName) {
                    node.detachEvent(ieName, func);
                }
            } else {
                node.removeEventListener(name, func, false);
            }
        }

        /**
         * Given an event from a script node, get the requirejs info from it,
         * and then removes the event listeners on the node.
         * @param {Event} evt
         * @returns {Object}
         */
        function getScriptData(evt) {
            //Using currentTarget instead of target for Firefox 2.0's sake. Not
            //all old browsers will be supported, but this one was easy enough
            //to support and still makes sense.
            var node = evt.currentTarget || evt.srcElement;

            //Remove the listeners once here.
            removeListener(node, context.onScriptLoad, 'load', 'onreadystatechange');
            removeListener(node, context.onScriptError, 'error');

            return {
                node: node,
                id: node && node.getAttribute('data-requiremodule')
            };
        }

        function intakeDefines() {
            var args;

            //Any defined modules in the global queue, intake them now.
            takeGlobalQueue();

            //Make sure any remaining defQueue items get properly processed.
            while (defQueue.length) {
                args = defQueue.shift();
                if (args[0] === null) {
                    return onError(makeError('mismatch', 'Mismatched anonymous define() module: ' + args[args.length - 1]));
                } else {
                    //args are id, deps, factory. Should be normalized by the
                    //define() function.
                    callGetModule(args);
                }
            }
        }

        context = {
            config: config,
            contextName: contextName,
            registry: registry,
            defined: defined,
            urlFetched: urlFetched,
            defQueue: defQueue,
            Module: Module,
            makeModuleMap: makeModuleMap,
            nextTick: req.nextTick,
            onError: onError,

            /**
             * Set a configuration for the context.
             * @param {Object} cfg config object to integrate.
             */
            configure: function (cfg) {
                //Make sure the baseUrl ends in a slash.
                if (cfg.baseUrl) {
                    if (cfg.baseUrl.charAt(cfg.baseUrl.length - 1) !== '/') {
                        cfg.baseUrl += '/';
                    }
                }

                //Save off the paths and packages since they require special processing,
                //they are additive.
                var pkgs = config.pkgs,
                    shim = config.shim,
                    objs = {
                        paths: true,
                        config: true,
                        map: true
                    };

                eachProp(cfg, function (value, prop) {
                    if (objs[prop]) {
                        if (prop === 'map') {
                            if (!config.map) {
                                config.map = {};
                            }
                            mixin(config[prop], value, true, true);
                        } else {
                            mixin(config[prop], value, true);
                        }
                    } else {
                        config[prop] = value;
                    }
                });

                //Merge shim
                if (cfg.shim) {
                    eachProp(cfg.shim, function (value, id) {
                        //Normalize the structure
                        if (isArray(value)) {
                            value = {
                                deps: value
                            };
                        }
                        if ((value.exports || value.init) && !value.exportsFn) {
                            value.exportsFn = context.makeShimExports(value);
                        }
                        shim[id] = value;
                    });
                    config.shim = shim;
                }

                //Adjust packages if necessary.
                if (cfg.packages) {
                    each(cfg.packages, function (pkgObj) {
                        var location;

                        pkgObj = typeof pkgObj === 'string' ? { name: pkgObj } : pkgObj;
                        location = pkgObj.location;

                        //Create a brand new object on pkgs, since currentPackages can
                        //be passed in again, and config.pkgs is the internal transformed
                        //state for all package configs.
                        pkgs[pkgObj.name] = {
                            name: pkgObj.name,
                            location: location || pkgObj.name,
                            //Remove leading dot in main, so main paths are normalized,
                            //and remove any trailing .js, since different package
                            //envs have different conventions: some use a module name,
                            //some use a file name.
                            main: (pkgObj.main || 'main')
                                  .replace(currDirRegExp, '')
                                  .replace(jsSuffixRegExp, '')
                        };
                    });

                    //Done with modifications, assing packages back to context config
                    config.pkgs = pkgs;
                }

                //If there are any "waiting to execute" modules in the registry,
                //update the maps for them, since their info, like URLs to load,
                //may have changed.
                eachProp(registry, function (mod, id) {
                    //If module already has init called, since it is too
                    //late to modify them, and ignore unnormalized ones
                    //since they are transient.
                    if (!mod.inited && !mod.map.unnormalized) {
                        mod.map = makeModuleMap(id);
                    }
                });

                //If a deps array or a config callback is specified, then call
                //require with those args. This is useful when require is defined as a
                //config object before require.js is loaded.
                if (cfg.deps || cfg.callback) {
                    context.require(cfg.deps || [], cfg.callback);
                }
            },

            makeShimExports: function (value) {
                function fn() {
                    var ret;
                    if (value.init) {
                        ret = value.init.apply(global, arguments);
                    }
                    return ret || (value.exports && getGlobal(value.exports));
                }
                return fn;
            },

            makeRequire: function (relMap, options) {
                options = options || {};

                function localRequire(deps, callback, errback) {
                    var id, map, requireMod;

                    if (options.enableBuildCallback && callback && isFunction(callback)) {
                        callback.__requireJsBuild = true;
                    }

                    if (typeof deps === 'string') {
                        if (isFunction(callback)) {
                            //Invalid call
                            return onError(makeError('requireargs', 'Invalid require call'), errback);
                        }

                        //If require|exports|module are requested, get the
                        //value for them from the special handlers. Caveat:
                        //this only works while module is being defined.
                        if (relMap && hasProp(handlers, deps)) {
                            return handlers[deps](registry[relMap.id]);
                        }

                        //Synchronous access to one module. If require.get is
                        //available (as in the Node adapter), prefer that.
                        if (req.get) {
                            return req.get(context, deps, relMap, localRequire);
                        }

                        //Normalize module name, if it contains . or ..
                        map = makeModuleMap(deps, relMap, false, true);
                        id = map.id;

                        if (!hasProp(defined, id)) {
                            return onError(makeError('notloaded', 'Module name "' +
                                        id +
                                        '" has not been loaded yet for context: ' +
                                        contextName +
                                        (relMap ? '' : '. Use require([])')));
                        }
                        return defined[id];
                    }

                    //Grab defines waiting in the global queue.
                    intakeDefines();

                    //Mark all the dependencies as needing to be loaded.
                    context.nextTick(function () {
                        //Some defines could have been added since the
                        //require call, collect them.
                        intakeDefines();

                        requireMod = getModule(makeModuleMap(null, relMap));

                        //Store if map config should be applied to this require
                        //call for dependencies.
                        requireMod.skipMap = options.skipMap;

                        requireMod.init(deps, callback, errback, {
                            enabled: true
                        });

                        checkLoaded();
                    });

                    return localRequire;
                }

                mixin(localRequire, {
                    isBrowser: isBrowser,

                    /**
                     * Converts a module name + .extension into an URL path.
                     * *Requires* the use of a module name. It does not support using
                     * plain URLs like nameToUrl.
                     */
                    toUrl: function (moduleNamePlusExt) {
                        var ext,
                            index = moduleNamePlusExt.lastIndexOf('.'),
                            segment = moduleNamePlusExt.split('/')[0],
                            isRelative = segment === '.' || segment === '..';

                        //Have a file extension alias, and it is not the
                        //dots from a relative path.
                        if (index !== -1 && (!isRelative || index > 1)) {
                            ext = moduleNamePlusExt.substring(index, moduleNamePlusExt.length);
                            moduleNamePlusExt = moduleNamePlusExt.substring(0, index);
                        }

                        return context.nameToUrl(normalize(moduleNamePlusExt,
                                                relMap && relMap.id, true), ext,  true);
                    },

                    defined: function (id) {
                        return hasProp(defined, makeModuleMap(id, relMap, false, true).id);
                    },

                    specified: function (id) {
                        id = makeModuleMap(id, relMap, false, true).id;
                        return hasProp(defined, id) || hasProp(registry, id);
                    }
                });

                //Only allow undef on top level require calls
                if (!relMap) {
                    localRequire.undef = function (id) {
                        //Bind any waiting define() calls to this context,
                        //fix for #408
                        takeGlobalQueue();

                        var map = makeModuleMap(id, relMap, true),
                            mod = getOwn(registry, id);

                        delete defined[id];
                        delete urlFetched[map.url];
                        delete undefEvents[id];

                        if (mod) {
                            //Hold on to listeners in case the
                            //module will be attempted to be reloaded
                            //using a different config.
                            if (mod.events.defined) {
                                undefEvents[id] = mod.events;
                            }

                            cleanRegistry(id);
                        }
                    };
                }

                return localRequire;
            },

            /**
             * Called to enable a module if it is still in the registry
             * awaiting enablement. A second arg, parent, the parent module,
             * is passed in for context, when this method is overriden by
             * the optimizer. Not shown here to keep code compact.
             */
            enable: function (depMap) {
                var mod = getOwn(registry, depMap.id);
                if (mod) {
                    getModule(depMap).enable();
                }
            },

            /**
             * Internal method used by environment adapters to complete a load event.
             * A load event could be a script load or just a load pass from a synchronous
             * load call.
             * @param {String} moduleName the name of the module to potentially complete.
             */
            completeLoad: function (moduleName) {
                var found, args, mod,
                    shim = getOwn(config.shim, moduleName) || {},
                    shExports = shim.exports;

                takeGlobalQueue();

                while (defQueue.length) {
                    args = defQueue.shift();
                    if (args[0] === null) {
                        args[0] = moduleName;
                        //If already found an anonymous module and bound it
                        //to this name, then this is some other anon module
                        //waiting for its completeLoad to fire.
                        if (found) {
                            break;
                        }
                        found = true;
                    } else if (args[0] === moduleName) {
                        //Found matching define call for this script!
                        found = true;
                    }

                    callGetModule(args);
                }

                //Do this after the cycle of callGetModule in case the result
                //of those calls/init calls changes the registry.
                mod = getOwn(registry, moduleName);

                if (!found && !hasProp(defined, moduleName) && mod && !mod.inited) {
                    if (config.enforceDefine && (!shExports || !getGlobal(shExports))) {
                        if (hasPathFallback(moduleName)) {
                            return;
                        } else {
                            return onError(makeError('nodefine',
                                             'No define call for ' + moduleName,
                                             null,
                                             [moduleName]));
                        }
                    } else {
                        //A script that does not call define(), so just simulate
                        //the call for it.
                        callGetModule([moduleName, (shim.deps || []), shim.exportsFn]);
                    }
                }

                checkLoaded();
            },

            /**
             * Converts a module name to a file path. Supports cases where
             * moduleName may actually be just an URL.
             * Note that it **does not** call normalize on the moduleName,
             * it is assumed to have already been normalized. This is an
             * internal API, not a public one. Use toUrl for the public API.
             */
            nameToUrl: function (moduleName, ext, skipExt) {
                var paths, pkgs, pkg, pkgPath, syms, i, parentModule, url,
                    parentPath;

                //If a colon is in the URL, it indicates a protocol is used and it is just
                //an URL to a file, or if it starts with a slash, contains a query arg (i.e. ?)
                //or ends with .js, then assume the user meant to use an url and not a module id.
                //The slash is important for protocol-less URLs as well as full paths.
                if (req.jsExtRegExp.test(moduleName)) {
                    //Just a plain path, not module name lookup, so just return it.
                    //Add extension if it is included. This is a bit wonky, only non-.js things pass
                    //an extension, this method probably needs to be reworked.
                    url = moduleName + (ext || '');
                } else {
                    //A module that needs to be converted to a path.
                    paths = config.paths;
                    pkgs = config.pkgs;

                    syms = moduleName.split('/');
                    //For each module name segment, see if there is a path
                    //registered for it. Start with most specific name
                    //and work up from it.
                    for (i = syms.length; i > 0; i -= 1) {
                        parentModule = syms.slice(0, i).join('/');
                        pkg = getOwn(pkgs, parentModule);
                        parentPath = getOwn(paths, parentModule);
                        if (parentPath) {
                            //If an array, it means there are a few choices,
                            //Choose the one that is desired
                            if (isArray(parentPath)) {
                                parentPath = parentPath[0];
                            }
                            syms.splice(0, i, parentPath);
                            break;
                        } else if (pkg) {
                            //If module name is just the package name, then looking
                            //for the main module.
                            if (moduleName === pkg.name) {
                                pkgPath = pkg.location + '/' + pkg.main;
                            } else {
                                pkgPath = pkg.location;
                            }
                            syms.splice(0, i, pkgPath);
                            break;
                        }
                    }

                    //Join the path parts together, then figure out if baseUrl is needed.
                    url = syms.join('/');
                    url += (ext || (/\?/.test(url) || skipExt ? '' : '.js'));
                    url = (url.charAt(0) === '/' || url.match(/^[\w\+\.\-]+:/) ? '' : config.baseUrl) + url;
                }

                return config.urlArgs ? url +
                                        ((url.indexOf('?') === -1 ? '?' : '&') +
                                         config.urlArgs) : url;
            },

            //Delegates to req.load. Broken out as a separate function to
            //allow overriding in the optimizer.
            load: function (id, url) {
                req.load(context, id, url);
            },

            /**
             * Executes a module callback function. Broken out as a separate function
             * solely to allow the build system to sequence the files in the built
             * layer in the right sequence.
             *
             * @private
             */
            execCb: function (name, callback, args, exports) {
                return callback.apply(exports, args);
            },

            /**
             * callback for script loads, used to check status of loading.
             *
             * @param {Event} evt the event from the browser for the script
             * that was loaded.
             */
            onScriptLoad: function (evt) {
                //Using currentTarget instead of target for Firefox 2.0's sake. Not
                //all old browsers will be supported, but this one was easy enough
                //to support and still makes sense.
                if (evt.type === 'load' ||
                        (readyRegExp.test((evt.currentTarget || evt.srcElement).readyState))) {
                    //Reset interactive script so a script node is not held onto for
                    //to long.
                    interactiveScript = null;

                    //Pull out the name of the module and the context.
                    var data = getScriptData(evt);
                    context.completeLoad(data.id);
                }
            },

            /**
             * Callback for script errors.
             */
            onScriptError: function (evt) {
                var data = getScriptData(evt);
                if (!hasPathFallback(data.id)) {
                    return onError(makeError('scripterror', 'Script error for: ' + data.id, evt, [data.id]));
                }
            }
        };

        context.require = context.makeRequire();
        return context;
    }

    /**
     * Main entry point.
     *
     * If the only argument to require is a string, then the module that
     * is represented by that string is fetched for the appropriate context.
     *
     * If the first argument is an array, then it will be treated as an array
     * of dependency string names to fetch. An optional function callback can
     * be specified to execute when all of those dependencies are available.
     *
     * Make a local req variable to help Caja compliance (it assumes things
     * on a require that are not standardized), and to give a short
     * name for minification/local scope use.
     */
    req = requirejs = function (deps, callback, errback, optional) {

        //Find the right context, use default
        var context, config,
            contextName = defContextName;

        // Determine if have config object in the call.
        if (!isArray(deps) && typeof deps !== 'string') {
            // deps is a config object
            config = deps;
            if (isArray(callback)) {
                // Adjust args if there are dependencies
                deps = callback;
                callback = errback;
                errback = optional;
            } else {
                deps = [];
            }
        }

        if (config && config.context) {
            contextName = config.context;
        }

        context = getOwn(contexts, contextName);
        if (!context) {
            context = contexts[contextName] = req.s.newContext(contextName);
        }

        if (config) {
            context.configure(config);
        }

        return context.require(deps, callback, errback);
    };

    /**
     * Support require.config() to make it easier to cooperate with other
     * AMD loaders on globally agreed names.
     */
    req.config = function (config) {
        return req(config);
    };

    /**
     * Execute something after the current tick
     * of the event loop. Override for other envs
     * that have a better solution than setTimeout.
     * @param  {Function} fn function to execute later.
     */
    req.nextTick = typeof setTimeout !== 'undefined' ? function (fn) {
        setTimeout(fn, 4);
    } : function (fn) { fn(); };

    /**
     * Export require as a global, but only if it does not already exist.
     */
    if (!require) {
        require = req;
    }

    req.version = version;

    //Used to filter out dependencies that are already paths.
    req.jsExtRegExp = /^\/|:|\?|\.js$/;
    req.isBrowser = isBrowser;
    s = req.s = {
        contexts: contexts,
        newContext: newContext
    };

    //Create default context.
    req({});

    //Exports some context-sensitive methods on global require.
    each([
        'toUrl',
        'undef',
        'defined',
        'specified'
    ], function (prop) {
        //Reference from contexts instead of early binding to default context,
        //so that during builds, the latest instance of the default context
        //with its config gets used.
        req[prop] = function () {
            var ctx = contexts[defContextName];
            return ctx.require[prop].apply(ctx, arguments);
        };
    });

    if (isBrowser) {
        head = s.head = document.getElementsByTagName('head')[0];
        //If BASE tag is in play, using appendChild is a problem for IE6.
        //When that browser dies, this can be removed. Details in this jQuery bug:
        //http://dev.jquery.com/ticket/2709
        baseElement = document.getElementsByTagName('base')[0];
        if (baseElement) {
            head = s.head = baseElement.parentNode;
        }
    }

    /**
     * Any errors that require explicitly generates will be passed to this
     * function. Intercept/override it if you want custom error handling.
     * @param {Error} err the error object.
     */
    req.onError = defaultOnError;

    /**
     * Creates the node for the load command. Only used in browser envs.
     */
    req.createNode = function (config, moduleName, url) {
        var node = config.xhtml ?
                document.createElementNS('http://www.w3.org/1999/xhtml', 'html:script') :
                document.createElement('script');
        node.type = config.scriptType || 'text/javascript';
        node.charset = 'utf-8';
        node.async = true;
        return node;
    };

    /**
     * Does the request to load a module for the browser case.
     * Make this a separate function to allow other environments
     * to override it.
     *
     * @param {Object} context the require context to find state.
     * @param {String} moduleName the name of the module.
     * @param {Object} url the URL to the module.
     */
    req.load = function (context, moduleName, url) {
        var config = (context && context.config) || {},
            node;
        if (isBrowser) {
            //In the browser so use a script tag
            node = req.createNode(config, moduleName, url);

            node.setAttribute('data-requirecontext', context.contextName);
            node.setAttribute('data-requiremodule', moduleName);

            //Set up load listener. Test attachEvent first because IE9 has
            //a subtle issue in its addEventListener and script onload firings
            //that do not match the behavior of all other browsers with
            //addEventListener support, which fire the onload event for a
            //script right after the script execution. See:
            //https://connect.microsoft.com/IE/feedback/details/648057/script-onload-event-is-not-fired-immediately-after-script-execution
            //UNFORTUNATELY Opera implements attachEvent but does not follow the script
            //script execution mode.
            if (node.attachEvent &&
                    //Check if node.attachEvent is artificially added by custom script or
                    //natively supported by browser
                    //read https://github.com/jrburke/requirejs/issues/187
                    //if we can NOT find [native code] then it must NOT natively supported.
                    //in IE8, node.attachEvent does not have toString()
                    //Note the test for "[native code" with no closing brace, see:
                    //https://github.com/jrburke/requirejs/issues/273
                    !(node.attachEvent.toString && node.attachEvent.toString().indexOf('[native code') < 0) &&
                    !isOpera) {
                //Probably IE. IE (at least 6-8) do not fire
                //script onload right after executing the script, so
                //we cannot tie the anonymous define call to a name.
                //However, IE reports the script as being in 'interactive'
                //readyState at the time of the define call.
                useInteractive = true;

                node.attachEvent('onreadystatechange', context.onScriptLoad);
                //It would be great to add an error handler here to catch
                //404s in IE9+. However, onreadystatechange will fire before
                //the error handler, so that does not help. If addEventListener
                //is used, then IE will fire error before load, but we cannot
                //use that pathway given the connect.microsoft.com issue
                //mentioned above about not doing the 'script execute,
                //then fire the script load event listener before execute
                //next script' that other browsers do.
                //Best hope: IE10 fixes the issues,
                //and then destroys all installs of IE 6-9.
                //node.attachEvent('onerror', context.onScriptError);
            } else {
                node.addEventListener('load', context.onScriptLoad, false);
                node.addEventListener('error', context.onScriptError, false);
            }
            node.src = url;

            //For some cache cases in IE 6-8, the script executes before the end
            //of the appendChild execution, so to tie an anonymous define
            //call to the module name (which is stored on the node), hold on
            //to a reference to this node, but clear after the DOM insertion.
            currentlyAddingScript = node;
            if (baseElement) {
                head.insertBefore(node, baseElement);
            } else {
                head.appendChild(node);
            }
            currentlyAddingScript = null;

            return node;
        } else if (isWebWorker) {
            try {
                //In a web worker, use importScripts. This is not a very
                //efficient use of importScripts, importScripts will block until
                //its script is downloaded and evaluated. However, if web workers
                //are in play, the expectation that a build has been done so that
                //only one script needs to be loaded anyway. This may need to be
                //reevaluated if other use cases become common.
                importScripts(url);

                //Account for anonymous modules
                context.completeLoad(moduleName);
            } catch (e) {
                context.onError(makeError('importscripts',
                                'importScripts failed for ' +
                                    moduleName + ' at ' + url,
                                e,
                                [moduleName]));
            }
        }
    };

    function getInteractiveScript() {
        if (interactiveScript && interactiveScript.readyState === 'interactive') {
            return interactiveScript;
        }

        eachReverse(scripts(), function (script) {
            if (script.readyState === 'interactive') {
                return (interactiveScript = script);
            }
        });
        return interactiveScript;
    }

    //Look for a data-main script attribute, which could also adjust the baseUrl.
    if (isBrowser) {
        //Figure out baseUrl. Get it from the script tag with require.js in it.
        eachReverse(scripts(), function (script) {
            //Set the 'head' where we can append children by
            //using the script's parent.
            if (!head) {
                head = script.parentNode;
            }

            //Look for a data-main attribute to set main script for the page
            //to load. If it is there, the path to data main becomes the
            //baseUrl, if it is not already set.
            dataMain = script.getAttribute('data-main');
            if (dataMain) {
                //Preserve dataMain in case it is a path (i.e. contains '?')
                mainScript = dataMain;

                //Set final baseUrl if there is not already an explicit one.
                if (!cfg.baseUrl) {
                    //Pull off the directory of data-main for use as the
                    //baseUrl.
                    src = mainScript.split('/');
                    mainScript = src.pop();
                    subPath = src.length ? src.join('/')  + '/' : './';

                    cfg.baseUrl = subPath;
                }

                //Strip off any trailing .js since mainScript is now
                //like a module name.
                mainScript = mainScript.replace(jsSuffixRegExp, '');

                 //If mainScript is still a path, fall back to dataMain
                if (req.jsExtRegExp.test(mainScript)) {
                    mainScript = dataMain;
                }

                //Put the data-main script in the files to load.
                cfg.deps = cfg.deps ? cfg.deps.concat(mainScript) : [mainScript];

                return true;
            }
        });
    }

    /**
     * The function that handles definitions of modules. Differs from
     * require() in that a string for the module should be the first argument,
     * and the function to execute after dependencies are loaded should
     * return a value to define the module corresponding to the first argument's
     * name.
     */
    define = function (name, deps, callback) {
        var node, context;

        //Allow for anonymous modules
        if (typeof name !== 'string') {
            //Adjust args appropriately
            callback = deps;
            deps = name;
            name = null;
        }

        //This module may not have dependencies
        if (!isArray(deps)) {
            callback = deps;
            deps = null;
        }

        //If no name, and callback is a function, then figure out if it a
        //CommonJS thing with dependencies.
        if (!deps && isFunction(callback)) {
            deps = [];
            //Remove comments from the callback string,
            //look for require calls, and pull them into the dependencies,
            //but only if there are function args.
            if (callback.length) {
                callback
                    .toString()
                    .replace(commentRegExp, '')
                    .replace(cjsRequireRegExp, function (match, dep) {
                        deps.push(dep);
                    });

                //May be a CommonJS thing even without require calls, but still
                //could use exports, and module. Avoid doing exports and module
                //work though if it just needs require.
                //REQUIRES the function to expect the CommonJS variables in the
                //order listed below.
                deps = (callback.length === 1 ? ['require'] : ['require', 'exports', 'module']).concat(deps);
            }
        }

        //If in IE 6-8 and hit an anonymous define() call, do the interactive
        //work.
        if (useInteractive) {
            node = currentlyAddingScript || getInteractiveScript();
            if (node) {
                if (!name) {
                    name = node.getAttribute('data-requiremodule');
                }
                context = contexts[node.getAttribute('data-requirecontext')];
            }
        }

        //Always save off evaluating the def call until the script onload handler.
        //This allows multiple modules to be in a file without prematurely
        //tracing dependencies, and allows for anonymous module support,
        //where the module name is not known until the script onload event
        //occurs. If no context, use the global queue, and get it processed
        //in the onscript load callback.
        (context ? context.defQueue : globalDefQueue).push([name, deps, callback]);
    };

    define.amd = {
        jQuery: true
    };


    /**
     * Executes the text. Normally just uses eval, but can be modified
     * to use a better, environment-specific call. Only used for transpiling
     * loader plugins, not for plain JS modules.
     * @param {String} text the text to execute/evaluate.
     */
    req.exec = function (text) {
        /*jslint evil: true */
        return eval(text);
    };

    //Set up with config info.
    req(cfg);
}(this));

define("requireLib", function(){});

/*! jQuery v2.0.3 | (c) 2005, 2013 jQuery Foundation, Inc. | jquery.org/license
//@ sourceMappingURL=jquery.min.map
*/
(function(e,undefined){var t,n,r=typeof undefined,i=e.location,o=e.document,s=o.documentElement,a=e.jQuery,u=e.$,l={},c=[],p="2.0.3",f=c.concat,h=c.push,d=c.slice,g=c.indexOf,m=l.toString,y=l.hasOwnProperty,v=p.trim,x=function(e,n){return new x.fn.init(e,n,t)},b=/[+-]?(?:\d*\.|)\d+(?:[eE][+-]?\d+|)/.source,w=/\S+/g,T=/^(?:\s*(<[\w\W]+>)[^>]*|#([\w-]*))$/,C=/^<(\w+)\s*\/?>(?:<\/\1>|)$/,k=/^-ms-/,N=/-([\da-z])/gi,E=function(e,t){return t.toUpperCase()},S=function(){o.removeEventListener("DOMContentLoaded",S,!1),e.removeEventListener("load",S,!1),x.ready()};x.fn=x.prototype={jquery:p,constructor:x,init:function(e,t,n){var r,i;if(!e)return this;if("string"==typeof e){if(r="<"===e.charAt(0)&&">"===e.charAt(e.length-1)&&e.length>=3?[null,e,null]:T.exec(e),!r||!r[1]&&t)return!t||t.jquery?(t||n).find(e):this.constructor(t).find(e);if(r[1]){if(t=t instanceof x?t[0]:t,x.merge(this,x.parseHTML(r[1],t&&t.nodeType?t.ownerDocument||t:o,!0)),C.test(r[1])&&x.isPlainObject(t))for(r in t)x.isFunction(this[r])?this[r](t[r]):this.attr(r,t[r]);return this}return i=o.getElementById(r[2]),i&&i.parentNode&&(this.length=1,this[0]=i),this.context=o,this.selector=e,this}return e.nodeType?(this.context=this[0]=e,this.length=1,this):x.isFunction(e)?n.ready(e):(e.selector!==undefined&&(this.selector=e.selector,this.context=e.context),x.makeArray(e,this))},selector:"",length:0,toArray:function(){return d.call(this)},get:function(e){return null==e?this.toArray():0>e?this[this.length+e]:this[e]},pushStack:function(e){var t=x.merge(this.constructor(),e);return t.prevObject=this,t.context=this.context,t},each:function(e,t){return x.each(this,e,t)},ready:function(e){return x.ready.promise().done(e),this},slice:function(){return this.pushStack(d.apply(this,arguments))},first:function(){return this.eq(0)},last:function(){return this.eq(-1)},eq:function(e){var t=this.length,n=+e+(0>e?t:0);return this.pushStack(n>=0&&t>n?[this[n]]:[])},map:function(e){return this.pushStack(x.map(this,function(t,n){return e.call(t,n,t)}))},end:function(){return this.prevObject||this.constructor(null)},push:h,sort:[].sort,splice:[].splice},x.fn.init.prototype=x.fn,x.extend=x.fn.extend=function(){var e,t,n,r,i,o,s=arguments[0]||{},a=1,u=arguments.length,l=!1;for("boolean"==typeof s&&(l=s,s=arguments[1]||{},a=2),"object"==typeof s||x.isFunction(s)||(s={}),u===a&&(s=this,--a);u>a;a++)if(null!=(e=arguments[a]))for(t in e)n=s[t],r=e[t],s!==r&&(l&&r&&(x.isPlainObject(r)||(i=x.isArray(r)))?(i?(i=!1,o=n&&x.isArray(n)?n:[]):o=n&&x.isPlainObject(n)?n:{},s[t]=x.extend(l,o,r)):r!==undefined&&(s[t]=r));return s},x.extend({expando:"jQuery"+(p+Math.random()).replace(/\D/g,""),noConflict:function(t){return e.$===x&&(e.$=u),t&&e.jQuery===x&&(e.jQuery=a),x},isReady:!1,readyWait:1,holdReady:function(e){e?x.readyWait++:x.ready(!0)},ready:function(e){(e===!0?--x.readyWait:x.isReady)||(x.isReady=!0,e!==!0&&--x.readyWait>0||(n.resolveWith(o,[x]),x.fn.trigger&&x(o).trigger("ready").off("ready")))},isFunction:function(e){return"function"===x.type(e)},isArray:Array.isArray,isWindow:function(e){return null!=e&&e===e.window},isNumeric:function(e){return!isNaN(parseFloat(e))&&isFinite(e)},type:function(e){return null==e?e+"":"object"==typeof e||"function"==typeof e?l[m.call(e)]||"object":typeof e},isPlainObject:function(e){if("object"!==x.type(e)||e.nodeType||x.isWindow(e))return!1;try{if(e.constructor&&!y.call(e.constructor.prototype,"isPrototypeOf"))return!1}catch(t){return!1}return!0},isEmptyObject:function(e){var t;for(t in e)return!1;return!0},error:function(e){throw Error(e)},parseHTML:function(e,t,n){if(!e||"string"!=typeof e)return null;"boolean"==typeof t&&(n=t,t=!1),t=t||o;var r=C.exec(e),i=!n&&[];return r?[t.createElement(r[1])]:(r=x.buildFragment([e],t,i),i&&x(i).remove(),x.merge([],r.childNodes))},parseJSON:JSON.parse,parseXML:function(e){var t,n;if(!e||"string"!=typeof e)return null;try{n=new DOMParser,t=n.parseFromString(e,"text/xml")}catch(r){t=undefined}return(!t||t.getElementsByTagName("parsererror").length)&&x.error("Invalid XML: "+e),t},noop:function(){},globalEval:function(e){var t,n=eval;e=x.trim(e),e&&(1===e.indexOf("use strict")?(t=o.createElement("script"),t.text=e,o.head.appendChild(t).parentNode.removeChild(t)):n(e))},camelCase:function(e){return e.replace(k,"ms-").replace(N,E)},nodeName:function(e,t){return e.nodeName&&e.nodeName.toLowerCase()===t.toLowerCase()},each:function(e,t,n){var r,i=0,o=e.length,s=j(e);if(n){if(s){for(;o>i;i++)if(r=t.apply(e[i],n),r===!1)break}else for(i in e)if(r=t.apply(e[i],n),r===!1)break}else if(s){for(;o>i;i++)if(r=t.call(e[i],i,e[i]),r===!1)break}else for(i in e)if(r=t.call(e[i],i,e[i]),r===!1)break;return e},trim:function(e){return null==e?"":v.call(e)},makeArray:function(e,t){var n=t||[];return null!=e&&(j(Object(e))?x.merge(n,"string"==typeof e?[e]:e):h.call(n,e)),n},inArray:function(e,t,n){return null==t?-1:g.call(t,e,n)},merge:function(e,t){var n=t.length,r=e.length,i=0;if("number"==typeof n)for(;n>i;i++)e[r++]=t[i];else while(t[i]!==undefined)e[r++]=t[i++];return e.length=r,e},grep:function(e,t,n){var r,i=[],o=0,s=e.length;for(n=!!n;s>o;o++)r=!!t(e[o],o),n!==r&&i.push(e[o]);return i},map:function(e,t,n){var r,i=0,o=e.length,s=j(e),a=[];if(s)for(;o>i;i++)r=t(e[i],i,n),null!=r&&(a[a.length]=r);else for(i in e)r=t(e[i],i,n),null!=r&&(a[a.length]=r);return f.apply([],a)},guid:1,proxy:function(e,t){var n,r,i;return"string"==typeof t&&(n=e[t],t=e,e=n),x.isFunction(e)?(r=d.call(arguments,2),i=function(){return e.apply(t||this,r.concat(d.call(arguments)))},i.guid=e.guid=e.guid||x.guid++,i):undefined},access:function(e,t,n,r,i,o,s){var a=0,u=e.length,l=null==n;if("object"===x.type(n)){i=!0;for(a in n)x.access(e,t,a,n[a],!0,o,s)}else if(r!==undefined&&(i=!0,x.isFunction(r)||(s=!0),l&&(s?(t.call(e,r),t=null):(l=t,t=function(e,t,n){return l.call(x(e),n)})),t))for(;u>a;a++)t(e[a],n,s?r:r.call(e[a],a,t(e[a],n)));return i?e:l?t.call(e):u?t(e[0],n):o},now:Date.now,swap:function(e,t,n,r){var i,o,s={};for(o in t)s[o]=e.style[o],e.style[o]=t[o];i=n.apply(e,r||[]);for(o in t)e.style[o]=s[o];return i}}),x.ready.promise=function(t){return n||(n=x.Deferred(),"complete"===o.readyState?setTimeout(x.ready):(o.addEventListener("DOMContentLoaded",S,!1),e.addEventListener("load",S,!1))),n.promise(t)},x.each("Boolean Number String Function Array Date RegExp Object Error".split(" "),function(e,t){l["[object "+t+"]"]=t.toLowerCase()});function j(e){var t=e.length,n=x.type(e);return x.isWindow(e)?!1:1===e.nodeType&&t?!0:"array"===n||"function"!==n&&(0===t||"number"==typeof t&&t>0&&t-1 in e)}t=x(o),function(e,undefined){var t,n,r,i,o,s,a,u,l,c,p,f,h,d,g,m,y,v="sizzle"+-new Date,b=e.document,w=0,T=0,C=st(),k=st(),N=st(),E=!1,S=function(e,t){return e===t?(E=!0,0):0},j=typeof undefined,D=1<<31,A={}.hasOwnProperty,L=[],q=L.pop,H=L.push,O=L.push,F=L.slice,P=L.indexOf||function(e){var t=0,n=this.length;for(;n>t;t++)if(this[t]===e)return t;return-1},R="checked|selected|async|autofocus|autoplay|controls|defer|disabled|hidden|ismap|loop|multiple|open|readonly|required|scoped",M="[\\x20\\t\\r\\n\\f]",W="(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+",$=W.replace("w","w#"),B="\\["+M+"*("+W+")"+M+"*(?:([*^$|!~]?=)"+M+"*(?:(['\"])((?:\\\\.|[^\\\\])*?)\\3|("+$+")|)|)"+M+"*\\]",I=":("+W+")(?:\\(((['\"])((?:\\\\.|[^\\\\])*?)\\3|((?:\\\\.|[^\\\\()[\\]]|"+B.replace(3,8)+")*)|.*)\\)|)",z=RegExp("^"+M+"+|((?:^|[^\\\\])(?:\\\\.)*)"+M+"+$","g"),_=RegExp("^"+M+"*,"+M+"*"),X=RegExp("^"+M+"*([>+~]|"+M+")"+M+"*"),U=RegExp(M+"*[+~]"),Y=RegExp("="+M+"*([^\\]'\"]*)"+M+"*\\]","g"),V=RegExp(I),G=RegExp("^"+$+"$"),J={ID:RegExp("^#("+W+")"),CLASS:RegExp("^\\.("+W+")"),TAG:RegExp("^("+W.replace("w","w*")+")"),ATTR:RegExp("^"+B),PSEUDO:RegExp("^"+I),CHILD:RegExp("^:(only|first|last|nth|nth-last)-(child|of-type)(?:\\("+M+"*(even|odd|(([+-]|)(\\d*)n|)"+M+"*(?:([+-]|)"+M+"*(\\d+)|))"+M+"*\\)|)","i"),bool:RegExp("^(?:"+R+")$","i"),needsContext:RegExp("^"+M+"*[>+~]|:(even|odd|eq|gt|lt|nth|first|last)(?:\\("+M+"*((?:-\\d)?\\d*)"+M+"*\\)|)(?=[^-]|$)","i")},Q=/^[^{]+\{\s*\[native \w/,K=/^(?:#([\w-]+)|(\w+)|\.([\w-]+))$/,Z=/^(?:input|select|textarea|button)$/i,et=/^h\d$/i,tt=/'|\\/g,nt=RegExp("\\\\([\\da-f]{1,6}"+M+"?|("+M+")|.)","ig"),rt=function(e,t,n){var r="0x"+t-65536;return r!==r||n?t:0>r?String.fromCharCode(r+65536):String.fromCharCode(55296|r>>10,56320|1023&r)};try{O.apply(L=F.call(b.childNodes),b.childNodes),L[b.childNodes.length].nodeType}catch(it){O={apply:L.length?function(e,t){H.apply(e,F.call(t))}:function(e,t){var n=e.length,r=0;while(e[n++]=t[r++]);e.length=n-1}}}function ot(e,t,r,i){var o,s,a,u,l,f,g,m,x,w;if((t?t.ownerDocument||t:b)!==p&&c(t),t=t||p,r=r||[],!e||"string"!=typeof e)return r;if(1!==(u=t.nodeType)&&9!==u)return[];if(h&&!i){if(o=K.exec(e))if(a=o[1]){if(9===u){if(s=t.getElementById(a),!s||!s.parentNode)return r;if(s.id===a)return r.push(s),r}else if(t.ownerDocument&&(s=t.ownerDocument.getElementById(a))&&y(t,s)&&s.id===a)return r.push(s),r}else{if(o[2])return O.apply(r,t.getElementsByTagName(e)),r;if((a=o[3])&&n.getElementsByClassName&&t.getElementsByClassName)return O.apply(r,t.getElementsByClassName(a)),r}if(n.qsa&&(!d||!d.test(e))){if(m=g=v,x=t,w=9===u&&e,1===u&&"object"!==t.nodeName.toLowerCase()){f=gt(e),(g=t.getAttribute("id"))?m=g.replace(tt,"\\$&"):t.setAttribute("id",m),m="[id='"+m+"'] ",l=f.length;while(l--)f[l]=m+mt(f[l]);x=U.test(e)&&t.parentNode||t,w=f.join(",")}if(w)try{return O.apply(r,x.querySelectorAll(w)),r}catch(T){}finally{g||t.removeAttribute("id")}}}return kt(e.replace(z,"$1"),t,r,i)}function st(){var e=[];function t(n,r){return e.push(n+=" ")>i.cacheLength&&delete t[e.shift()],t[n]=r}return t}function at(e){return e[v]=!0,e}function ut(e){var t=p.createElement("div");try{return!!e(t)}catch(n){return!1}finally{t.parentNode&&t.parentNode.removeChild(t),t=null}}function lt(e,t){var n=e.split("|"),r=e.length;while(r--)i.attrHandle[n[r]]=t}function ct(e,t){var n=t&&e,r=n&&1===e.nodeType&&1===t.nodeType&&(~t.sourceIndex||D)-(~e.sourceIndex||D);if(r)return r;if(n)while(n=n.nextSibling)if(n===t)return-1;return e?1:-1}function pt(e){return function(t){var n=t.nodeName.toLowerCase();return"input"===n&&t.type===e}}function ft(e){return function(t){var n=t.nodeName.toLowerCase();return("input"===n||"button"===n)&&t.type===e}}function ht(e){return at(function(t){return t=+t,at(function(n,r){var i,o=e([],n.length,t),s=o.length;while(s--)n[i=o[s]]&&(n[i]=!(r[i]=n[i]))})})}s=ot.isXML=function(e){var t=e&&(e.ownerDocument||e).documentElement;return t?"HTML"!==t.nodeName:!1},n=ot.support={},c=ot.setDocument=function(e){var t=e?e.ownerDocument||e:b,r=t.defaultView;return t!==p&&9===t.nodeType&&t.documentElement?(p=t,f=t.documentElement,h=!s(t),r&&r.attachEvent&&r!==r.top&&r.attachEvent("onbeforeunload",function(){c()}),n.attributes=ut(function(e){return e.className="i",!e.getAttribute("className")}),n.getElementsByTagName=ut(function(e){return e.appendChild(t.createComment("")),!e.getElementsByTagName("*").length}),n.getElementsByClassName=ut(function(e){return e.innerHTML="<div class='a'></div><div class='a i'></div>",e.firstChild.className="i",2===e.getElementsByClassName("i").length}),n.getById=ut(function(e){return f.appendChild(e).id=v,!t.getElementsByName||!t.getElementsByName(v).length}),n.getById?(i.find.ID=function(e,t){if(typeof t.getElementById!==j&&h){var n=t.getElementById(e);return n&&n.parentNode?[n]:[]}},i.filter.ID=function(e){var t=e.replace(nt,rt);return function(e){return e.getAttribute("id")===t}}):(delete i.find.ID,i.filter.ID=function(e){var t=e.replace(nt,rt);return function(e){var n=typeof e.getAttributeNode!==j&&e.getAttributeNode("id");return n&&n.value===t}}),i.find.TAG=n.getElementsByTagName?function(e,t){return typeof t.getElementsByTagName!==j?t.getElementsByTagName(e):undefined}:function(e,t){var n,r=[],i=0,o=t.getElementsByTagName(e);if("*"===e){while(n=o[i++])1===n.nodeType&&r.push(n);return r}return o},i.find.CLASS=n.getElementsByClassName&&function(e,t){return typeof t.getElementsByClassName!==j&&h?t.getElementsByClassName(e):undefined},g=[],d=[],(n.qsa=Q.test(t.querySelectorAll))&&(ut(function(e){e.innerHTML="<select><option selected=''></option></select>",e.querySelectorAll("[selected]").length||d.push("\\["+M+"*(?:value|"+R+")"),e.querySelectorAll(":checked").length||d.push(":checked")}),ut(function(e){var n=t.createElement("input");n.setAttribute("type","hidden"),e.appendChild(n).setAttribute("t",""),e.querySelectorAll("[t^='']").length&&d.push("[*^$]="+M+"*(?:''|\"\")"),e.querySelectorAll(":enabled").length||d.push(":enabled",":disabled"),e.querySelectorAll("*,:x"),d.push(",.*:")})),(n.matchesSelector=Q.test(m=f.webkitMatchesSelector||f.mozMatchesSelector||f.oMatchesSelector||f.msMatchesSelector))&&ut(function(e){n.disconnectedMatch=m.call(e,"div"),m.call(e,"[s!='']:x"),g.push("!=",I)}),d=d.length&&RegExp(d.join("|")),g=g.length&&RegExp(g.join("|")),y=Q.test(f.contains)||f.compareDocumentPosition?function(e,t){var n=9===e.nodeType?e.documentElement:e,r=t&&t.parentNode;return e===r||!(!r||1!==r.nodeType||!(n.contains?n.contains(r):e.compareDocumentPosition&&16&e.compareDocumentPosition(r)))}:function(e,t){if(t)while(t=t.parentNode)if(t===e)return!0;return!1},S=f.compareDocumentPosition?function(e,r){if(e===r)return E=!0,0;var i=r.compareDocumentPosition&&e.compareDocumentPosition&&e.compareDocumentPosition(r);return i?1&i||!n.sortDetached&&r.compareDocumentPosition(e)===i?e===t||y(b,e)?-1:r===t||y(b,r)?1:l?P.call(l,e)-P.call(l,r):0:4&i?-1:1:e.compareDocumentPosition?-1:1}:function(e,n){var r,i=0,o=e.parentNode,s=n.parentNode,a=[e],u=[n];if(e===n)return E=!0,0;if(!o||!s)return e===t?-1:n===t?1:o?-1:s?1:l?P.call(l,e)-P.call(l,n):0;if(o===s)return ct(e,n);r=e;while(r=r.parentNode)a.unshift(r);r=n;while(r=r.parentNode)u.unshift(r);while(a[i]===u[i])i++;return i?ct(a[i],u[i]):a[i]===b?-1:u[i]===b?1:0},t):p},ot.matches=function(e,t){return ot(e,null,null,t)},ot.matchesSelector=function(e,t){if((e.ownerDocument||e)!==p&&c(e),t=t.replace(Y,"='$1']"),!(!n.matchesSelector||!h||g&&g.test(t)||d&&d.test(t)))try{var r=m.call(e,t);if(r||n.disconnectedMatch||e.document&&11!==e.document.nodeType)return r}catch(i){}return ot(t,p,null,[e]).length>0},ot.contains=function(e,t){return(e.ownerDocument||e)!==p&&c(e),y(e,t)},ot.attr=function(e,t){(e.ownerDocument||e)!==p&&c(e);var r=i.attrHandle[t.toLowerCase()],o=r&&A.call(i.attrHandle,t.toLowerCase())?r(e,t,!h):undefined;return o===undefined?n.attributes||!h?e.getAttribute(t):(o=e.getAttributeNode(t))&&o.specified?o.value:null:o},ot.error=function(e){throw Error("Syntax error, unrecognized expression: "+e)},ot.uniqueSort=function(e){var t,r=[],i=0,o=0;if(E=!n.detectDuplicates,l=!n.sortStable&&e.slice(0),e.sort(S),E){while(t=e[o++])t===e[o]&&(i=r.push(o));while(i--)e.splice(r[i],1)}return e},o=ot.getText=function(e){var t,n="",r=0,i=e.nodeType;if(i){if(1===i||9===i||11===i){if("string"==typeof e.textContent)return e.textContent;for(e=e.firstChild;e;e=e.nextSibling)n+=o(e)}else if(3===i||4===i)return e.nodeValue}else for(;t=e[r];r++)n+=o(t);return n},i=ot.selectors={cacheLength:50,createPseudo:at,match:J,attrHandle:{},find:{},relative:{">":{dir:"parentNode",first:!0}," ":{dir:"parentNode"},"+":{dir:"previousSibling",first:!0},"~":{dir:"previousSibling"}},preFilter:{ATTR:function(e){return e[1]=e[1].replace(nt,rt),e[3]=(e[4]||e[5]||"").replace(nt,rt),"~="===e[2]&&(e[3]=" "+e[3]+" "),e.slice(0,4)},CHILD:function(e){return e[1]=e[1].toLowerCase(),"nth"===e[1].slice(0,3)?(e[3]||ot.error(e[0]),e[4]=+(e[4]?e[5]+(e[6]||1):2*("even"===e[3]||"odd"===e[3])),e[5]=+(e[7]+e[8]||"odd"===e[3])):e[3]&&ot.error(e[0]),e},PSEUDO:function(e){var t,n=!e[5]&&e[2];return J.CHILD.test(e[0])?null:(e[3]&&e[4]!==undefined?e[2]=e[4]:n&&V.test(n)&&(t=gt(n,!0))&&(t=n.indexOf(")",n.length-t)-n.length)&&(e[0]=e[0].slice(0,t),e[2]=n.slice(0,t)),e.slice(0,3))}},filter:{TAG:function(e){var t=e.replace(nt,rt).toLowerCase();return"*"===e?function(){return!0}:function(e){return e.nodeName&&e.nodeName.toLowerCase()===t}},CLASS:function(e){var t=C[e+" "];return t||(t=RegExp("(^|"+M+")"+e+"("+M+"|$)"))&&C(e,function(e){return t.test("string"==typeof e.className&&e.className||typeof e.getAttribute!==j&&e.getAttribute("class")||"")})},ATTR:function(e,t,n){return function(r){var i=ot.attr(r,e);return null==i?"!="===t:t?(i+="","="===t?i===n:"!="===t?i!==n:"^="===t?n&&0===i.indexOf(n):"*="===t?n&&i.indexOf(n)>-1:"$="===t?n&&i.slice(-n.length)===n:"~="===t?(" "+i+" ").indexOf(n)>-1:"|="===t?i===n||i.slice(0,n.length+1)===n+"-":!1):!0}},CHILD:function(e,t,n,r,i){var o="nth"!==e.slice(0,3),s="last"!==e.slice(-4),a="of-type"===t;return 1===r&&0===i?function(e){return!!e.parentNode}:function(t,n,u){var l,c,p,f,h,d,g=o!==s?"nextSibling":"previousSibling",m=t.parentNode,y=a&&t.nodeName.toLowerCase(),x=!u&&!a;if(m){if(o){while(g){p=t;while(p=p[g])if(a?p.nodeName.toLowerCase()===y:1===p.nodeType)return!1;d=g="only"===e&&!d&&"nextSibling"}return!0}if(d=[s?m.firstChild:m.lastChild],s&&x){c=m[v]||(m[v]={}),l=c[e]||[],h=l[0]===w&&l[1],f=l[0]===w&&l[2],p=h&&m.childNodes[h];while(p=++h&&p&&p[g]||(f=h=0)||d.pop())if(1===p.nodeType&&++f&&p===t){c[e]=[w,h,f];break}}else if(x&&(l=(t[v]||(t[v]={}))[e])&&l[0]===w)f=l[1];else while(p=++h&&p&&p[g]||(f=h=0)||d.pop())if((a?p.nodeName.toLowerCase()===y:1===p.nodeType)&&++f&&(x&&((p[v]||(p[v]={}))[e]=[w,f]),p===t))break;return f-=i,f===r||0===f%r&&f/r>=0}}},PSEUDO:function(e,t){var n,r=i.pseudos[e]||i.setFilters[e.toLowerCase()]||ot.error("unsupported pseudo: "+e);return r[v]?r(t):r.length>1?(n=[e,e,"",t],i.setFilters.hasOwnProperty(e.toLowerCase())?at(function(e,n){var i,o=r(e,t),s=o.length;while(s--)i=P.call(e,o[s]),e[i]=!(n[i]=o[s])}):function(e){return r(e,0,n)}):r}},pseudos:{not:at(function(e){var t=[],n=[],r=a(e.replace(z,"$1"));return r[v]?at(function(e,t,n,i){var o,s=r(e,null,i,[]),a=e.length;while(a--)(o=s[a])&&(e[a]=!(t[a]=o))}):function(e,i,o){return t[0]=e,r(t,null,o,n),!n.pop()}}),has:at(function(e){return function(t){return ot(e,t).length>0}}),contains:at(function(e){return function(t){return(t.textContent||t.innerText||o(t)).indexOf(e)>-1}}),lang:at(function(e){return G.test(e||"")||ot.error("unsupported lang: "+e),e=e.replace(nt,rt).toLowerCase(),function(t){var n;do if(n=h?t.lang:t.getAttribute("xml:lang")||t.getAttribute("lang"))return n=n.toLowerCase(),n===e||0===n.indexOf(e+"-");while((t=t.parentNode)&&1===t.nodeType);return!1}}),target:function(t){var n=e.location&&e.location.hash;return n&&n.slice(1)===t.id},root:function(e){return e===f},focus:function(e){return e===p.activeElement&&(!p.hasFocus||p.hasFocus())&&!!(e.type||e.href||~e.tabIndex)},enabled:function(e){return e.disabled===!1},disabled:function(e){return e.disabled===!0},checked:function(e){var t=e.nodeName.toLowerCase();return"input"===t&&!!e.checked||"option"===t&&!!e.selected},selected:function(e){return e.parentNode&&e.parentNode.selectedIndex,e.selected===!0},empty:function(e){for(e=e.firstChild;e;e=e.nextSibling)if(e.nodeName>"@"||3===e.nodeType||4===e.nodeType)return!1;return!0},parent:function(e){return!i.pseudos.empty(e)},header:function(e){return et.test(e.nodeName)},input:function(e){return Z.test(e.nodeName)},button:function(e){var t=e.nodeName.toLowerCase();return"input"===t&&"button"===e.type||"button"===t},text:function(e){var t;return"input"===e.nodeName.toLowerCase()&&"text"===e.type&&(null==(t=e.getAttribute("type"))||t.toLowerCase()===e.type)},first:ht(function(){return[0]}),last:ht(function(e,t){return[t-1]}),eq:ht(function(e,t,n){return[0>n?n+t:n]}),even:ht(function(e,t){var n=0;for(;t>n;n+=2)e.push(n);return e}),odd:ht(function(e,t){var n=1;for(;t>n;n+=2)e.push(n);return e}),lt:ht(function(e,t,n){var r=0>n?n+t:n;for(;--r>=0;)e.push(r);return e}),gt:ht(function(e,t,n){var r=0>n?n+t:n;for(;t>++r;)e.push(r);return e})}},i.pseudos.nth=i.pseudos.eq;for(t in{radio:!0,checkbox:!0,file:!0,password:!0,image:!0})i.pseudos[t]=pt(t);for(t in{submit:!0,reset:!0})i.pseudos[t]=ft(t);function dt(){}dt.prototype=i.filters=i.pseudos,i.setFilters=new dt;function gt(e,t){var n,r,o,s,a,u,l,c=k[e+" "];if(c)return t?0:c.slice(0);a=e,u=[],l=i.preFilter;while(a){(!n||(r=_.exec(a)))&&(r&&(a=a.slice(r[0].length)||a),u.push(o=[])),n=!1,(r=X.exec(a))&&(n=r.shift(),o.push({value:n,type:r[0].replace(z," ")}),a=a.slice(n.length));for(s in i.filter)!(r=J[s].exec(a))||l[s]&&!(r=l[s](r))||(n=r.shift(),o.push({value:n,type:s,matches:r}),a=a.slice(n.length));if(!n)break}return t?a.length:a?ot.error(e):k(e,u).slice(0)}function mt(e){var t=0,n=e.length,r="";for(;n>t;t++)r+=e[t].value;return r}function yt(e,t,n){var i=t.dir,o=n&&"parentNode"===i,s=T++;return t.first?function(t,n,r){while(t=t[i])if(1===t.nodeType||o)return e(t,n,r)}:function(t,n,a){var u,l,c,p=w+" "+s;if(a){while(t=t[i])if((1===t.nodeType||o)&&e(t,n,a))return!0}else while(t=t[i])if(1===t.nodeType||o)if(c=t[v]||(t[v]={}),(l=c[i])&&l[0]===p){if((u=l[1])===!0||u===r)return u===!0}else if(l=c[i]=[p],l[1]=e(t,n,a)||r,l[1]===!0)return!0}}function vt(e){return e.length>1?function(t,n,r){var i=e.length;while(i--)if(!e[i](t,n,r))return!1;return!0}:e[0]}function xt(e,t,n,r,i){var o,s=[],a=0,u=e.length,l=null!=t;for(;u>a;a++)(o=e[a])&&(!n||n(o,r,i))&&(s.push(o),l&&t.push(a));return s}function bt(e,t,n,r,i,o){return r&&!r[v]&&(r=bt(r)),i&&!i[v]&&(i=bt(i,o)),at(function(o,s,a,u){var l,c,p,f=[],h=[],d=s.length,g=o||Ct(t||"*",a.nodeType?[a]:a,[]),m=!e||!o&&t?g:xt(g,f,e,a,u),y=n?i||(o?e:d||r)?[]:s:m;if(n&&n(m,y,a,u),r){l=xt(y,h),r(l,[],a,u),c=l.length;while(c--)(p=l[c])&&(y[h[c]]=!(m[h[c]]=p))}if(o){if(i||e){if(i){l=[],c=y.length;while(c--)(p=y[c])&&l.push(m[c]=p);i(null,y=[],l,u)}c=y.length;while(c--)(p=y[c])&&(l=i?P.call(o,p):f[c])>-1&&(o[l]=!(s[l]=p))}}else y=xt(y===s?y.splice(d,y.length):y),i?i(null,s,y,u):O.apply(s,y)})}function wt(e){var t,n,r,o=e.length,s=i.relative[e[0].type],a=s||i.relative[" "],l=s?1:0,c=yt(function(e){return e===t},a,!0),p=yt(function(e){return P.call(t,e)>-1},a,!0),f=[function(e,n,r){return!s&&(r||n!==u)||((t=n).nodeType?c(e,n,r):p(e,n,r))}];for(;o>l;l++)if(n=i.relative[e[l].type])f=[yt(vt(f),n)];else{if(n=i.filter[e[l].type].apply(null,e[l].matches),n[v]){for(r=++l;o>r;r++)if(i.relative[e[r].type])break;return bt(l>1&&vt(f),l>1&&mt(e.slice(0,l-1).concat({value:" "===e[l-2].type?"*":""})).replace(z,"$1"),n,r>l&&wt(e.slice(l,r)),o>r&&wt(e=e.slice(r)),o>r&&mt(e))}f.push(n)}return vt(f)}function Tt(e,t){var n=0,o=t.length>0,s=e.length>0,a=function(a,l,c,f,h){var d,g,m,y=[],v=0,x="0",b=a&&[],T=null!=h,C=u,k=a||s&&i.find.TAG("*",h&&l.parentNode||l),N=w+=null==C?1:Math.random()||.1;for(T&&(u=l!==p&&l,r=n);null!=(d=k[x]);x++){if(s&&d){g=0;while(m=e[g++])if(m(d,l,c)){f.push(d);break}T&&(w=N,r=++n)}o&&((d=!m&&d)&&v--,a&&b.push(d))}if(v+=x,o&&x!==v){g=0;while(m=t[g++])m(b,y,l,c);if(a){if(v>0)while(x--)b[x]||y[x]||(y[x]=q.call(f));y=xt(y)}O.apply(f,y),T&&!a&&y.length>0&&v+t.length>1&&ot.uniqueSort(f)}return T&&(w=N,u=C),b};return o?at(a):a}a=ot.compile=function(e,t){var n,r=[],i=[],o=N[e+" "];if(!o){t||(t=gt(e)),n=t.length;while(n--)o=wt(t[n]),o[v]?r.push(o):i.push(o);o=N(e,Tt(i,r))}return o};function Ct(e,t,n){var r=0,i=t.length;for(;i>r;r++)ot(e,t[r],n);return n}function kt(e,t,r,o){var s,u,l,c,p,f=gt(e);if(!o&&1===f.length){if(u=f[0]=f[0].slice(0),u.length>2&&"ID"===(l=u[0]).type&&n.getById&&9===t.nodeType&&h&&i.relative[u[1].type]){if(t=(i.find.ID(l.matches[0].replace(nt,rt),t)||[])[0],!t)return r;e=e.slice(u.shift().value.length)}s=J.needsContext.test(e)?0:u.length;while(s--){if(l=u[s],i.relative[c=l.type])break;if((p=i.find[c])&&(o=p(l.matches[0].replace(nt,rt),U.test(u[0].type)&&t.parentNode||t))){if(u.splice(s,1),e=o.length&&mt(u),!e)return O.apply(r,o),r;break}}}return a(e,f)(o,t,!h,r,U.test(e)),r}n.sortStable=v.split("").sort(S).join("")===v,n.detectDuplicates=E,c(),n.sortDetached=ut(function(e){return 1&e.compareDocumentPosition(p.createElement("div"))}),ut(function(e){return e.innerHTML="<a href='#'></a>","#"===e.firstChild.getAttribute("href")})||lt("type|href|height|width",function(e,t,n){return n?undefined:e.getAttribute(t,"type"===t.toLowerCase()?1:2)}),n.attributes&&ut(function(e){return e.innerHTML="<input/>",e.firstChild.setAttribute("value",""),""===e.firstChild.getAttribute("value")})||lt("value",function(e,t,n){return n||"input"!==e.nodeName.toLowerCase()?undefined:e.defaultValue}),ut(function(e){return null==e.getAttribute("disabled")})||lt(R,function(e,t,n){var r;return n?undefined:(r=e.getAttributeNode(t))&&r.specified?r.value:e[t]===!0?t.toLowerCase():null}),x.find=ot,x.expr=ot.selectors,x.expr[":"]=x.expr.pseudos,x.unique=ot.uniqueSort,x.text=ot.getText,x.isXMLDoc=ot.isXML,x.contains=ot.contains}(e);var D={};function A(e){var t=D[e]={};return x.each(e.match(w)||[],function(e,n){t[n]=!0}),t}x.Callbacks=function(e){e="string"==typeof e?D[e]||A(e):x.extend({},e);var t,n,r,i,o,s,a=[],u=!e.once&&[],l=function(p){for(t=e.memory&&p,n=!0,s=i||0,i=0,o=a.length,r=!0;a&&o>s;s++)if(a[s].apply(p[0],p[1])===!1&&e.stopOnFalse){t=!1;break}r=!1,a&&(u?u.length&&l(u.shift()):t?a=[]:c.disable())},c={add:function(){if(a){var n=a.length;(function s(t){x.each(t,function(t,n){var r=x.type(n);"function"===r?e.unique&&c.has(n)||a.push(n):n&&n.length&&"string"!==r&&s(n)})})(arguments),r?o=a.length:t&&(i=n,l(t))}return this},remove:function(){return a&&x.each(arguments,function(e,t){var n;while((n=x.inArray(t,a,n))>-1)a.splice(n,1),r&&(o>=n&&o--,s>=n&&s--)}),this},has:function(e){return e?x.inArray(e,a)>-1:!(!a||!a.length)},empty:function(){return a=[],o=0,this},disable:function(){return a=u=t=undefined,this},disabled:function(){return!a},lock:function(){return u=undefined,t||c.disable(),this},locked:function(){return!u},fireWith:function(e,t){return!a||n&&!u||(t=t||[],t=[e,t.slice?t.slice():t],r?u.push(t):l(t)),this},fire:function(){return c.fireWith(this,arguments),this},fired:function(){return!!n}};return c},x.extend({Deferred:function(e){var t=[["resolve","done",x.Callbacks("once memory"),"resolved"],["reject","fail",x.Callbacks("once memory"),"rejected"],["notify","progress",x.Callbacks("memory")]],n="pending",r={state:function(){return n},always:function(){return i.done(arguments).fail(arguments),this},then:function(){var e=arguments;return x.Deferred(function(n){x.each(t,function(t,o){var s=o[0],a=x.isFunction(e[t])&&e[t];i[o[1]](function(){var e=a&&a.apply(this,arguments);e&&x.isFunction(e.promise)?e.promise().done(n.resolve).fail(n.reject).progress(n.notify):n[s+"With"](this===r?n.promise():this,a?[e]:arguments)})}),e=null}).promise()},promise:function(e){return null!=e?x.extend(e,r):r}},i={};return r.pipe=r.then,x.each(t,function(e,o){var s=o[2],a=o[3];r[o[1]]=s.add,a&&s.add(function(){n=a},t[1^e][2].disable,t[2][2].lock),i[o[0]]=function(){return i[o[0]+"With"](this===i?r:this,arguments),this},i[o[0]+"With"]=s.fireWith}),r.promise(i),e&&e.call(i,i),i},when:function(e){var t=0,n=d.call(arguments),r=n.length,i=1!==r||e&&x.isFunction(e.promise)?r:0,o=1===i?e:x.Deferred(),s=function(e,t,n){return function(r){t[e]=this,n[e]=arguments.length>1?d.call(arguments):r,n===a?o.notifyWith(t,n):--i||o.resolveWith(t,n)}},a,u,l;if(r>1)for(a=Array(r),u=Array(r),l=Array(r);r>t;t++)n[t]&&x.isFunction(n[t].promise)?n[t].promise().done(s(t,l,n)).fail(o.reject).progress(s(t,u,a)):--i;return i||o.resolveWith(l,n),o.promise()}}),x.support=function(t){var n=o.createElement("input"),r=o.createDocumentFragment(),i=o.createElement("div"),s=o.createElement("select"),a=s.appendChild(o.createElement("option"));return n.type?(n.type="checkbox",t.checkOn=""!==n.value,t.optSelected=a.selected,t.reliableMarginRight=!0,t.boxSizingReliable=!0,t.pixelPosition=!1,n.checked=!0,t.noCloneChecked=n.cloneNode(!0).checked,s.disabled=!0,t.optDisabled=!a.disabled,n=o.createElement("input"),n.value="t",n.type="radio",t.radioValue="t"===n.value,n.setAttribute("checked","t"),n.setAttribute("name","t"),r.appendChild(n),t.checkClone=r.cloneNode(!0).cloneNode(!0).lastChild.checked,t.focusinBubbles="onfocusin"in e,i.style.backgroundClip="content-box",i.cloneNode(!0).style.backgroundClip="",t.clearCloneStyle="content-box"===i.style.backgroundClip,x(function(){var n,r,s="padding:0;margin:0;border:0;display:block;-webkit-box-sizing:content-box;-moz-box-sizing:content-box;box-sizing:content-box",a=o.getElementsByTagName("body")[0];a&&(n=o.createElement("div"),n.style.cssText="border:0;width:0;height:0;position:absolute;top:0;left:-9999px;margin-top:1px",a.appendChild(n).appendChild(i),i.innerHTML="",i.style.cssText="-webkit-box-sizing:border-box;-moz-box-sizing:border-box;box-sizing:border-box;padding:1px;border:1px;display:block;width:4px;margin-top:1%;position:absolute;top:1%",x.swap(a,null!=a.style.zoom?{zoom:1}:{},function(){t.boxSizing=4===i.offsetWidth}),e.getComputedStyle&&(t.pixelPosition="1%"!==(e.getComputedStyle(i,null)||{}).top,t.boxSizingReliable="4px"===(e.getComputedStyle(i,null)||{width:"4px"}).width,r=i.appendChild(o.createElement("div")),r.style.cssText=i.style.cssText=s,r.style.marginRight=r.style.width="0",i.style.width="1px",t.reliableMarginRight=!parseFloat((e.getComputedStyle(r,null)||{}).marginRight)),a.removeChild(n))}),t):t}({});var L,q,H=/(?:\{[\s\S]*\}|\[[\s\S]*\])$/,O=/([A-Z])/g;function F(){Object.defineProperty(this.cache={},0,{get:function(){return{}}}),this.expando=x.expando+Math.random()}F.uid=1,F.accepts=function(e){return e.nodeType?1===e.nodeType||9===e.nodeType:!0},F.prototype={key:function(e){if(!F.accepts(e))return 0;var t={},n=e[this.expando];if(!n){n=F.uid++;try{t[this.expando]={value:n},Object.defineProperties(e,t)}catch(r){t[this.expando]=n,x.extend(e,t)}}return this.cache[n]||(this.cache[n]={}),n},set:function(e,t,n){var r,i=this.key(e),o=this.cache[i];if("string"==typeof t)o[t]=n;else if(x.isEmptyObject(o))x.extend(this.cache[i],t);else for(r in t)o[r]=t[r];return o},get:function(e,t){var n=this.cache[this.key(e)];return t===undefined?n:n[t]},access:function(e,t,n){var r;return t===undefined||t&&"string"==typeof t&&n===undefined?(r=this.get(e,t),r!==undefined?r:this.get(e,x.camelCase(t))):(this.set(e,t,n),n!==undefined?n:t)},remove:function(e,t){var n,r,i,o=this.key(e),s=this.cache[o];if(t===undefined)this.cache[o]={};else{x.isArray(t)?r=t.concat(t.map(x.camelCase)):(i=x.camelCase(t),t in s?r=[t,i]:(r=i,r=r in s?[r]:r.match(w)||[])),n=r.length;while(n--)delete s[r[n]]}},hasData:function(e){return!x.isEmptyObject(this.cache[e[this.expando]]||{})},discard:function(e){e[this.expando]&&delete this.cache[e[this.expando]]}},L=new F,q=new F,x.extend({acceptData:F.accepts,hasData:function(e){return L.hasData(e)||q.hasData(e)},data:function(e,t,n){return L.access(e,t,n)},removeData:function(e,t){L.remove(e,t)},_data:function(e,t,n){return q.access(e,t,n)},_removeData:function(e,t){q.remove(e,t)}}),x.fn.extend({data:function(e,t){var n,r,i=this[0],o=0,s=null;if(e===undefined){if(this.length&&(s=L.get(i),1===i.nodeType&&!q.get(i,"hasDataAttrs"))){for(n=i.attributes;n.length>o;o++)r=n[o].name,0===r.indexOf("data-")&&(r=x.camelCase(r.slice(5)),P(i,r,s[r]));q.set(i,"hasDataAttrs",!0)}return s}return"object"==typeof e?this.each(function(){L.set(this,e)}):x.access(this,function(t){var n,r=x.camelCase(e);if(i&&t===undefined){if(n=L.get(i,e),n!==undefined)return n;if(n=L.get(i,r),n!==undefined)return n;if(n=P(i,r,undefined),n!==undefined)return n}else this.each(function(){var n=L.get(this,r);L.set(this,r,t),-1!==e.indexOf("-")&&n!==undefined&&L.set(this,e,t)})},null,t,arguments.length>1,null,!0)},removeData:function(e){return this.each(function(){L.remove(this,e)})}});function P(e,t,n){var r;if(n===undefined&&1===e.nodeType)if(r="data-"+t.replace(O,"-$1").toLowerCase(),n=e.getAttribute(r),"string"==typeof n){try{n="true"===n?!0:"false"===n?!1:"null"===n?null:+n+""===n?+n:H.test(n)?JSON.parse(n):n}catch(i){}L.set(e,t,n)}else n=undefined;return n}x.extend({queue:function(e,t,n){var r;return e?(t=(t||"fx")+"queue",r=q.get(e,t),n&&(!r||x.isArray(n)?r=q.access(e,t,x.makeArray(n)):r.push(n)),r||[]):undefined},dequeue:function(e,t){t=t||"fx";var n=x.queue(e,t),r=n.length,i=n.shift(),o=x._queueHooks(e,t),s=function(){x.dequeue(e,t)
};"inprogress"===i&&(i=n.shift(),r--),i&&("fx"===t&&n.unshift("inprogress"),delete o.stop,i.call(e,s,o)),!r&&o&&o.empty.fire()},_queueHooks:function(e,t){var n=t+"queueHooks";return q.get(e,n)||q.access(e,n,{empty:x.Callbacks("once memory").add(function(){q.remove(e,[t+"queue",n])})})}}),x.fn.extend({queue:function(e,t){var n=2;return"string"!=typeof e&&(t=e,e="fx",n--),n>arguments.length?x.queue(this[0],e):t===undefined?this:this.each(function(){var n=x.queue(this,e,t);x._queueHooks(this,e),"fx"===e&&"inprogress"!==n[0]&&x.dequeue(this,e)})},dequeue:function(e){return this.each(function(){x.dequeue(this,e)})},delay:function(e,t){return e=x.fx?x.fx.speeds[e]||e:e,t=t||"fx",this.queue(t,function(t,n){var r=setTimeout(t,e);n.stop=function(){clearTimeout(r)}})},clearQueue:function(e){return this.queue(e||"fx",[])},promise:function(e,t){var n,r=1,i=x.Deferred(),o=this,s=this.length,a=function(){--r||i.resolveWith(o,[o])};"string"!=typeof e&&(t=e,e=undefined),e=e||"fx";while(s--)n=q.get(o[s],e+"queueHooks"),n&&n.empty&&(r++,n.empty.add(a));return a(),i.promise(t)}});var R,M,W=/[\t\r\n\f]/g,$=/\r/g,B=/^(?:input|select|textarea|button)$/i;x.fn.extend({attr:function(e,t){return x.access(this,x.attr,e,t,arguments.length>1)},removeAttr:function(e){return this.each(function(){x.removeAttr(this,e)})},prop:function(e,t){return x.access(this,x.prop,e,t,arguments.length>1)},removeProp:function(e){return this.each(function(){delete this[x.propFix[e]||e]})},addClass:function(e){var t,n,r,i,o,s=0,a=this.length,u="string"==typeof e&&e;if(x.isFunction(e))return this.each(function(t){x(this).addClass(e.call(this,t,this.className))});if(u)for(t=(e||"").match(w)||[];a>s;s++)if(n=this[s],r=1===n.nodeType&&(n.className?(" "+n.className+" ").replace(W," "):" ")){o=0;while(i=t[o++])0>r.indexOf(" "+i+" ")&&(r+=i+" ");n.className=x.trim(r)}return this},removeClass:function(e){var t,n,r,i,o,s=0,a=this.length,u=0===arguments.length||"string"==typeof e&&e;if(x.isFunction(e))return this.each(function(t){x(this).removeClass(e.call(this,t,this.className))});if(u)for(t=(e||"").match(w)||[];a>s;s++)if(n=this[s],r=1===n.nodeType&&(n.className?(" "+n.className+" ").replace(W," "):"")){o=0;while(i=t[o++])while(r.indexOf(" "+i+" ")>=0)r=r.replace(" "+i+" "," ");n.className=e?x.trim(r):""}return this},toggleClass:function(e,t){var n=typeof e;return"boolean"==typeof t&&"string"===n?t?this.addClass(e):this.removeClass(e):x.isFunction(e)?this.each(function(n){x(this).toggleClass(e.call(this,n,this.className,t),t)}):this.each(function(){if("string"===n){var t,i=0,o=x(this),s=e.match(w)||[];while(t=s[i++])o.hasClass(t)?o.removeClass(t):o.addClass(t)}else(n===r||"boolean"===n)&&(this.className&&q.set(this,"__className__",this.className),this.className=this.className||e===!1?"":q.get(this,"__className__")||"")})},hasClass:function(e){var t=" "+e+" ",n=0,r=this.length;for(;r>n;n++)if(1===this[n].nodeType&&(" "+this[n].className+" ").replace(W," ").indexOf(t)>=0)return!0;return!1},val:function(e){var t,n,r,i=this[0];{if(arguments.length)return r=x.isFunction(e),this.each(function(n){var i;1===this.nodeType&&(i=r?e.call(this,n,x(this).val()):e,null==i?i="":"number"==typeof i?i+="":x.isArray(i)&&(i=x.map(i,function(e){return null==e?"":e+""})),t=x.valHooks[this.type]||x.valHooks[this.nodeName.toLowerCase()],t&&"set"in t&&t.set(this,i,"value")!==undefined||(this.value=i))});if(i)return t=x.valHooks[i.type]||x.valHooks[i.nodeName.toLowerCase()],t&&"get"in t&&(n=t.get(i,"value"))!==undefined?n:(n=i.value,"string"==typeof n?n.replace($,""):null==n?"":n)}}}),x.extend({valHooks:{option:{get:function(e){var t=e.attributes.value;return!t||t.specified?e.value:e.text}},select:{get:function(e){var t,n,r=e.options,i=e.selectedIndex,o="select-one"===e.type||0>i,s=o?null:[],a=o?i+1:r.length,u=0>i?a:o?i:0;for(;a>u;u++)if(n=r[u],!(!n.selected&&u!==i||(x.support.optDisabled?n.disabled:null!==n.getAttribute("disabled"))||n.parentNode.disabled&&x.nodeName(n.parentNode,"optgroup"))){if(t=x(n).val(),o)return t;s.push(t)}return s},set:function(e,t){var n,r,i=e.options,o=x.makeArray(t),s=i.length;while(s--)r=i[s],(r.selected=x.inArray(x(r).val(),o)>=0)&&(n=!0);return n||(e.selectedIndex=-1),o}}},attr:function(e,t,n){var i,o,s=e.nodeType;if(e&&3!==s&&8!==s&&2!==s)return typeof e.getAttribute===r?x.prop(e,t,n):(1===s&&x.isXMLDoc(e)||(t=t.toLowerCase(),i=x.attrHooks[t]||(x.expr.match.bool.test(t)?M:R)),n===undefined?i&&"get"in i&&null!==(o=i.get(e,t))?o:(o=x.find.attr(e,t),null==o?undefined:o):null!==n?i&&"set"in i&&(o=i.set(e,n,t))!==undefined?o:(e.setAttribute(t,n+""),n):(x.removeAttr(e,t),undefined))},removeAttr:function(e,t){var n,r,i=0,o=t&&t.match(w);if(o&&1===e.nodeType)while(n=o[i++])r=x.propFix[n]||n,x.expr.match.bool.test(n)&&(e[r]=!1),e.removeAttribute(n)},attrHooks:{type:{set:function(e,t){if(!x.support.radioValue&&"radio"===t&&x.nodeName(e,"input")){var n=e.value;return e.setAttribute("type",t),n&&(e.value=n),t}}}},propFix:{"for":"htmlFor","class":"className"},prop:function(e,t,n){var r,i,o,s=e.nodeType;if(e&&3!==s&&8!==s&&2!==s)return o=1!==s||!x.isXMLDoc(e),o&&(t=x.propFix[t]||t,i=x.propHooks[t]),n!==undefined?i&&"set"in i&&(r=i.set(e,n,t))!==undefined?r:e[t]=n:i&&"get"in i&&null!==(r=i.get(e,t))?r:e[t]},propHooks:{tabIndex:{get:function(e){return e.hasAttribute("tabindex")||B.test(e.nodeName)||e.href?e.tabIndex:-1}}}}),M={set:function(e,t,n){return t===!1?x.removeAttr(e,n):e.setAttribute(n,n),n}},x.each(x.expr.match.bool.source.match(/\w+/g),function(e,t){var n=x.expr.attrHandle[t]||x.find.attr;x.expr.attrHandle[t]=function(e,t,r){var i=x.expr.attrHandle[t],o=r?undefined:(x.expr.attrHandle[t]=undefined)!=n(e,t,r)?t.toLowerCase():null;return x.expr.attrHandle[t]=i,o}}),x.support.optSelected||(x.propHooks.selected={get:function(e){var t=e.parentNode;return t&&t.parentNode&&t.parentNode.selectedIndex,null}}),x.each(["tabIndex","readOnly","maxLength","cellSpacing","cellPadding","rowSpan","colSpan","useMap","frameBorder","contentEditable"],function(){x.propFix[this.toLowerCase()]=this}),x.each(["radio","checkbox"],function(){x.valHooks[this]={set:function(e,t){return x.isArray(t)?e.checked=x.inArray(x(e).val(),t)>=0:undefined}},x.support.checkOn||(x.valHooks[this].get=function(e){return null===e.getAttribute("value")?"on":e.value})});var I=/^key/,z=/^(?:mouse|contextmenu)|click/,_=/^(?:focusinfocus|focusoutblur)$/,X=/^([^.]*)(?:\.(.+)|)$/;function U(){return!0}function Y(){return!1}function V(){try{return o.activeElement}catch(e){}}x.event={global:{},add:function(e,t,n,i,o){var s,a,u,l,c,p,f,h,d,g,m,y=q.get(e);if(y){n.handler&&(s=n,n=s.handler,o=s.selector),n.guid||(n.guid=x.guid++),(l=y.events)||(l=y.events={}),(a=y.handle)||(a=y.handle=function(e){return typeof x===r||e&&x.event.triggered===e.type?undefined:x.event.dispatch.apply(a.elem,arguments)},a.elem=e),t=(t||"").match(w)||[""],c=t.length;while(c--)u=X.exec(t[c])||[],d=m=u[1],g=(u[2]||"").split(".").sort(),d&&(f=x.event.special[d]||{},d=(o?f.delegateType:f.bindType)||d,f=x.event.special[d]||{},p=x.extend({type:d,origType:m,data:i,handler:n,guid:n.guid,selector:o,needsContext:o&&x.expr.match.needsContext.test(o),namespace:g.join(".")},s),(h=l[d])||(h=l[d]=[],h.delegateCount=0,f.setup&&f.setup.call(e,i,g,a)!==!1||e.addEventListener&&e.addEventListener(d,a,!1)),f.add&&(f.add.call(e,p),p.handler.guid||(p.handler.guid=n.guid)),o?h.splice(h.delegateCount++,0,p):h.push(p),x.event.global[d]=!0);e=null}},remove:function(e,t,n,r,i){var o,s,a,u,l,c,p,f,h,d,g,m=q.hasData(e)&&q.get(e);if(m&&(u=m.events)){t=(t||"").match(w)||[""],l=t.length;while(l--)if(a=X.exec(t[l])||[],h=g=a[1],d=(a[2]||"").split(".").sort(),h){p=x.event.special[h]||{},h=(r?p.delegateType:p.bindType)||h,f=u[h]||[],a=a[2]&&RegExp("(^|\\.)"+d.join("\\.(?:.*\\.|)")+"(\\.|$)"),s=o=f.length;while(o--)c=f[o],!i&&g!==c.origType||n&&n.guid!==c.guid||a&&!a.test(c.namespace)||r&&r!==c.selector&&("**"!==r||!c.selector)||(f.splice(o,1),c.selector&&f.delegateCount--,p.remove&&p.remove.call(e,c));s&&!f.length&&(p.teardown&&p.teardown.call(e,d,m.handle)!==!1||x.removeEvent(e,h,m.handle),delete u[h])}else for(h in u)x.event.remove(e,h+t[l],n,r,!0);x.isEmptyObject(u)&&(delete m.handle,q.remove(e,"events"))}},trigger:function(t,n,r,i){var s,a,u,l,c,p,f,h=[r||o],d=y.call(t,"type")?t.type:t,g=y.call(t,"namespace")?t.namespace.split("."):[];if(a=u=r=r||o,3!==r.nodeType&&8!==r.nodeType&&!_.test(d+x.event.triggered)&&(d.indexOf(".")>=0&&(g=d.split("."),d=g.shift(),g.sort()),c=0>d.indexOf(":")&&"on"+d,t=t[x.expando]?t:new x.Event(d,"object"==typeof t&&t),t.isTrigger=i?2:3,t.namespace=g.join("."),t.namespace_re=t.namespace?RegExp("(^|\\.)"+g.join("\\.(?:.*\\.|)")+"(\\.|$)"):null,t.result=undefined,t.target||(t.target=r),n=null==n?[t]:x.makeArray(n,[t]),f=x.event.special[d]||{},i||!f.trigger||f.trigger.apply(r,n)!==!1)){if(!i&&!f.noBubble&&!x.isWindow(r)){for(l=f.delegateType||d,_.test(l+d)||(a=a.parentNode);a;a=a.parentNode)h.push(a),u=a;u===(r.ownerDocument||o)&&h.push(u.defaultView||u.parentWindow||e)}s=0;while((a=h[s++])&&!t.isPropagationStopped())t.type=s>1?l:f.bindType||d,p=(q.get(a,"events")||{})[t.type]&&q.get(a,"handle"),p&&p.apply(a,n),p=c&&a[c],p&&x.acceptData(a)&&p.apply&&p.apply(a,n)===!1&&t.preventDefault();return t.type=d,i||t.isDefaultPrevented()||f._default&&f._default.apply(h.pop(),n)!==!1||!x.acceptData(r)||c&&x.isFunction(r[d])&&!x.isWindow(r)&&(u=r[c],u&&(r[c]=null),x.event.triggered=d,r[d](),x.event.triggered=undefined,u&&(r[c]=u)),t.result}},dispatch:function(e){e=x.event.fix(e);var t,n,r,i,o,s=[],a=d.call(arguments),u=(q.get(this,"events")||{})[e.type]||[],l=x.event.special[e.type]||{};if(a[0]=e,e.delegateTarget=this,!l.preDispatch||l.preDispatch.call(this,e)!==!1){s=x.event.handlers.call(this,e,u),t=0;while((i=s[t++])&&!e.isPropagationStopped()){e.currentTarget=i.elem,n=0;while((o=i.handlers[n++])&&!e.isImmediatePropagationStopped())(!e.namespace_re||e.namespace_re.test(o.namespace))&&(e.handleObj=o,e.data=o.data,r=((x.event.special[o.origType]||{}).handle||o.handler).apply(i.elem,a),r!==undefined&&(e.result=r)===!1&&(e.preventDefault(),e.stopPropagation()))}return l.postDispatch&&l.postDispatch.call(this,e),e.result}},handlers:function(e,t){var n,r,i,o,s=[],a=t.delegateCount,u=e.target;if(a&&u.nodeType&&(!e.button||"click"!==e.type))for(;u!==this;u=u.parentNode||this)if(u.disabled!==!0||"click"!==e.type){for(r=[],n=0;a>n;n++)o=t[n],i=o.selector+" ",r[i]===undefined&&(r[i]=o.needsContext?x(i,this).index(u)>=0:x.find(i,this,null,[u]).length),r[i]&&r.push(o);r.length&&s.push({elem:u,handlers:r})}return t.length>a&&s.push({elem:this,handlers:t.slice(a)}),s},props:"altKey bubbles cancelable ctrlKey currentTarget eventPhase metaKey relatedTarget shiftKey target timeStamp view which".split(" "),fixHooks:{},keyHooks:{props:"char charCode key keyCode".split(" "),filter:function(e,t){return null==e.which&&(e.which=null!=t.charCode?t.charCode:t.keyCode),e}},mouseHooks:{props:"button buttons clientX clientY offsetX offsetY pageX pageY screenX screenY toElement".split(" "),filter:function(e,t){var n,r,i,s=t.button;return null==e.pageX&&null!=t.clientX&&(n=e.target.ownerDocument||o,r=n.documentElement,i=n.body,e.pageX=t.clientX+(r&&r.scrollLeft||i&&i.scrollLeft||0)-(r&&r.clientLeft||i&&i.clientLeft||0),e.pageY=t.clientY+(r&&r.scrollTop||i&&i.scrollTop||0)-(r&&r.clientTop||i&&i.clientTop||0)),e.which||s===undefined||(e.which=1&s?1:2&s?3:4&s?2:0),e}},fix:function(e){if(e[x.expando])return e;var t,n,r,i=e.type,s=e,a=this.fixHooks[i];a||(this.fixHooks[i]=a=z.test(i)?this.mouseHooks:I.test(i)?this.keyHooks:{}),r=a.props?this.props.concat(a.props):this.props,e=new x.Event(s),t=r.length;while(t--)n=r[t],e[n]=s[n];return e.target||(e.target=o),3===e.target.nodeType&&(e.target=e.target.parentNode),a.filter?a.filter(e,s):e},special:{load:{noBubble:!0},focus:{trigger:function(){return this!==V()&&this.focus?(this.focus(),!1):undefined},delegateType:"focusin"},blur:{trigger:function(){return this===V()&&this.blur?(this.blur(),!1):undefined},delegateType:"focusout"},click:{trigger:function(){return"checkbox"===this.type&&this.click&&x.nodeName(this,"input")?(this.click(),!1):undefined},_default:function(e){return x.nodeName(e.target,"a")}},beforeunload:{postDispatch:function(e){e.result!==undefined&&(e.originalEvent.returnValue=e.result)}}},simulate:function(e,t,n,r){var i=x.extend(new x.Event,n,{type:e,isSimulated:!0,originalEvent:{}});r?x.event.trigger(i,null,t):x.event.dispatch.call(t,i),i.isDefaultPrevented()&&n.preventDefault()}},x.removeEvent=function(e,t,n){e.removeEventListener&&e.removeEventListener(t,n,!1)},x.Event=function(e,t){return this instanceof x.Event?(e&&e.type?(this.originalEvent=e,this.type=e.type,this.isDefaultPrevented=e.defaultPrevented||e.getPreventDefault&&e.getPreventDefault()?U:Y):this.type=e,t&&x.extend(this,t),this.timeStamp=e&&e.timeStamp||x.now(),this[x.expando]=!0,undefined):new x.Event(e,t)},x.Event.prototype={isDefaultPrevented:Y,isPropagationStopped:Y,isImmediatePropagationStopped:Y,preventDefault:function(){var e=this.originalEvent;this.isDefaultPrevented=U,e&&e.preventDefault&&e.preventDefault()},stopPropagation:function(){var e=this.originalEvent;this.isPropagationStopped=U,e&&e.stopPropagation&&e.stopPropagation()},stopImmediatePropagation:function(){this.isImmediatePropagationStopped=U,this.stopPropagation()}},x.each({mouseenter:"mouseover",mouseleave:"mouseout"},function(e,t){x.event.special[e]={delegateType:t,bindType:t,handle:function(e){var n,r=this,i=e.relatedTarget,o=e.handleObj;return(!i||i!==r&&!x.contains(r,i))&&(e.type=o.origType,n=o.handler.apply(this,arguments),e.type=t),n}}}),x.support.focusinBubbles||x.each({focus:"focusin",blur:"focusout"},function(e,t){var n=0,r=function(e){x.event.simulate(t,e.target,x.event.fix(e),!0)};x.event.special[t]={setup:function(){0===n++&&o.addEventListener(e,r,!0)},teardown:function(){0===--n&&o.removeEventListener(e,r,!0)}}}),x.fn.extend({on:function(e,t,n,r,i){var o,s;if("object"==typeof e){"string"!=typeof t&&(n=n||t,t=undefined);for(s in e)this.on(s,t,n,e[s],i);return this}if(null==n&&null==r?(r=t,n=t=undefined):null==r&&("string"==typeof t?(r=n,n=undefined):(r=n,n=t,t=undefined)),r===!1)r=Y;else if(!r)return this;return 1===i&&(o=r,r=function(e){return x().off(e),o.apply(this,arguments)},r.guid=o.guid||(o.guid=x.guid++)),this.each(function(){x.event.add(this,e,r,n,t)})},one:function(e,t,n,r){return this.on(e,t,n,r,1)},off:function(e,t,n){var r,i;if(e&&e.preventDefault&&e.handleObj)return r=e.handleObj,x(e.delegateTarget).off(r.namespace?r.origType+"."+r.namespace:r.origType,r.selector,r.handler),this;if("object"==typeof e){for(i in e)this.off(i,t,e[i]);return this}return(t===!1||"function"==typeof t)&&(n=t,t=undefined),n===!1&&(n=Y),this.each(function(){x.event.remove(this,e,n,t)})},trigger:function(e,t){return this.each(function(){x.event.trigger(e,t,this)})},triggerHandler:function(e,t){var n=this[0];return n?x.event.trigger(e,t,n,!0):undefined}});var G=/^.[^:#\[\.,]*$/,J=/^(?:parents|prev(?:Until|All))/,Q=x.expr.match.needsContext,K={children:!0,contents:!0,next:!0,prev:!0};x.fn.extend({find:function(e){var t,n=[],r=this,i=r.length;if("string"!=typeof e)return this.pushStack(x(e).filter(function(){for(t=0;i>t;t++)if(x.contains(r[t],this))return!0}));for(t=0;i>t;t++)x.find(e,r[t],n);return n=this.pushStack(i>1?x.unique(n):n),n.selector=this.selector?this.selector+" "+e:e,n},has:function(e){var t=x(e,this),n=t.length;return this.filter(function(){var e=0;for(;n>e;e++)if(x.contains(this,t[e]))return!0})},not:function(e){return this.pushStack(et(this,e||[],!0))},filter:function(e){return this.pushStack(et(this,e||[],!1))},is:function(e){return!!et(this,"string"==typeof e&&Q.test(e)?x(e):e||[],!1).length},closest:function(e,t){var n,r=0,i=this.length,o=[],s=Q.test(e)||"string"!=typeof e?x(e,t||this.context):0;for(;i>r;r++)for(n=this[r];n&&n!==t;n=n.parentNode)if(11>n.nodeType&&(s?s.index(n)>-1:1===n.nodeType&&x.find.matchesSelector(n,e))){n=o.push(n);break}return this.pushStack(o.length>1?x.unique(o):o)},index:function(e){return e?"string"==typeof e?g.call(x(e),this[0]):g.call(this,e.jquery?e[0]:e):this[0]&&this[0].parentNode?this.first().prevAll().length:-1},add:function(e,t){var n="string"==typeof e?x(e,t):x.makeArray(e&&e.nodeType?[e]:e),r=x.merge(this.get(),n);return this.pushStack(x.unique(r))},addBack:function(e){return this.add(null==e?this.prevObject:this.prevObject.filter(e))}});function Z(e,t){while((e=e[t])&&1!==e.nodeType);return e}x.each({parent:function(e){var t=e.parentNode;return t&&11!==t.nodeType?t:null},parents:function(e){return x.dir(e,"parentNode")},parentsUntil:function(e,t,n){return x.dir(e,"parentNode",n)},next:function(e){return Z(e,"nextSibling")},prev:function(e){return Z(e,"previousSibling")},nextAll:function(e){return x.dir(e,"nextSibling")},prevAll:function(e){return x.dir(e,"previousSibling")},nextUntil:function(e,t,n){return x.dir(e,"nextSibling",n)},prevUntil:function(e,t,n){return x.dir(e,"previousSibling",n)},siblings:function(e){return x.sibling((e.parentNode||{}).firstChild,e)},children:function(e){return x.sibling(e.firstChild)},contents:function(e){return e.contentDocument||x.merge([],e.childNodes)}},function(e,t){x.fn[e]=function(n,r){var i=x.map(this,t,n);return"Until"!==e.slice(-5)&&(r=n),r&&"string"==typeof r&&(i=x.filter(r,i)),this.length>1&&(K[e]||x.unique(i),J.test(e)&&i.reverse()),this.pushStack(i)}}),x.extend({filter:function(e,t,n){var r=t[0];return n&&(e=":not("+e+")"),1===t.length&&1===r.nodeType?x.find.matchesSelector(r,e)?[r]:[]:x.find.matches(e,x.grep(t,function(e){return 1===e.nodeType}))},dir:function(e,t,n){var r=[],i=n!==undefined;while((e=e[t])&&9!==e.nodeType)if(1===e.nodeType){if(i&&x(e).is(n))break;r.push(e)}return r},sibling:function(e,t){var n=[];for(;e;e=e.nextSibling)1===e.nodeType&&e!==t&&n.push(e);return n}});function et(e,t,n){if(x.isFunction(t))return x.grep(e,function(e,r){return!!t.call(e,r,e)!==n});if(t.nodeType)return x.grep(e,function(e){return e===t!==n});if("string"==typeof t){if(G.test(t))return x.filter(t,e,n);t=x.filter(t,e)}return x.grep(e,function(e){return g.call(t,e)>=0!==n})}var tt=/<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/gi,nt=/<([\w:]+)/,rt=/<|&#?\w+;/,it=/<(?:script|style|link)/i,ot=/^(?:checkbox|radio)$/i,st=/checked\s*(?:[^=]|=\s*.checked.)/i,at=/^$|\/(?:java|ecma)script/i,ut=/^true\/(.*)/,lt=/^\s*<!(?:\[CDATA\[|--)|(?:\]\]|--)>\s*$/g,ct={option:[1,"<select multiple='multiple'>","</select>"],thead:[1,"<table>","</table>"],col:[2,"<table><colgroup>","</colgroup></table>"],tr:[2,"<table><tbody>","</tbody></table>"],td:[3,"<table><tbody><tr>","</tr></tbody></table>"],_default:[0,"",""]};ct.optgroup=ct.option,ct.tbody=ct.tfoot=ct.colgroup=ct.caption=ct.thead,ct.th=ct.td,x.fn.extend({text:function(e){return x.access(this,function(e){return e===undefined?x.text(this):this.empty().append((this[0]&&this[0].ownerDocument||o).createTextNode(e))},null,e,arguments.length)},append:function(){return this.domManip(arguments,function(e){if(1===this.nodeType||11===this.nodeType||9===this.nodeType){var t=pt(this,e);t.appendChild(e)}})},prepend:function(){return this.domManip(arguments,function(e){if(1===this.nodeType||11===this.nodeType||9===this.nodeType){var t=pt(this,e);t.insertBefore(e,t.firstChild)}})},before:function(){return this.domManip(arguments,function(e){this.parentNode&&this.parentNode.insertBefore(e,this)})},after:function(){return this.domManip(arguments,function(e){this.parentNode&&this.parentNode.insertBefore(e,this.nextSibling)})},remove:function(e,t){var n,r=e?x.filter(e,this):this,i=0;for(;null!=(n=r[i]);i++)t||1!==n.nodeType||x.cleanData(mt(n)),n.parentNode&&(t&&x.contains(n.ownerDocument,n)&&dt(mt(n,"script")),n.parentNode.removeChild(n));return this},empty:function(){var e,t=0;for(;null!=(e=this[t]);t++)1===e.nodeType&&(x.cleanData(mt(e,!1)),e.textContent="");return this},clone:function(e,t){return e=null==e?!1:e,t=null==t?e:t,this.map(function(){return x.clone(this,e,t)})},html:function(e){return x.access(this,function(e){var t=this[0]||{},n=0,r=this.length;if(e===undefined&&1===t.nodeType)return t.innerHTML;if("string"==typeof e&&!it.test(e)&&!ct[(nt.exec(e)||["",""])[1].toLowerCase()]){e=e.replace(tt,"<$1></$2>");try{for(;r>n;n++)t=this[n]||{},1===t.nodeType&&(x.cleanData(mt(t,!1)),t.innerHTML=e);t=0}catch(i){}}t&&this.empty().append(e)},null,e,arguments.length)},replaceWith:function(){var e=x.map(this,function(e){return[e.nextSibling,e.parentNode]}),t=0;return this.domManip(arguments,function(n){var r=e[t++],i=e[t++];i&&(r&&r.parentNode!==i&&(r=this.nextSibling),x(this).remove(),i.insertBefore(n,r))},!0),t?this:this.remove()},detach:function(e){return this.remove(e,!0)},domManip:function(e,t,n){e=f.apply([],e);var r,i,o,s,a,u,l=0,c=this.length,p=this,h=c-1,d=e[0],g=x.isFunction(d);if(g||!(1>=c||"string"!=typeof d||x.support.checkClone)&&st.test(d))return this.each(function(r){var i=p.eq(r);g&&(e[0]=d.call(this,r,i.html())),i.domManip(e,t,n)});if(c&&(r=x.buildFragment(e,this[0].ownerDocument,!1,!n&&this),i=r.firstChild,1===r.childNodes.length&&(r=i),i)){for(o=x.map(mt(r,"script"),ft),s=o.length;c>l;l++)a=r,l!==h&&(a=x.clone(a,!0,!0),s&&x.merge(o,mt(a,"script"))),t.call(this[l],a,l);if(s)for(u=o[o.length-1].ownerDocument,x.map(o,ht),l=0;s>l;l++)a=o[l],at.test(a.type||"")&&!q.access(a,"globalEval")&&x.contains(u,a)&&(a.src?x._evalUrl(a.src):x.globalEval(a.textContent.replace(lt,"")))}return this}}),x.each({appendTo:"append",prependTo:"prepend",insertBefore:"before",insertAfter:"after",replaceAll:"replaceWith"},function(e,t){x.fn[e]=function(e){var n,r=[],i=x(e),o=i.length-1,s=0;for(;o>=s;s++)n=s===o?this:this.clone(!0),x(i[s])[t](n),h.apply(r,n.get());return this.pushStack(r)}}),x.extend({clone:function(e,t,n){var r,i,o,s,a=e.cloneNode(!0),u=x.contains(e.ownerDocument,e);if(!(x.support.noCloneChecked||1!==e.nodeType&&11!==e.nodeType||x.isXMLDoc(e)))for(s=mt(a),o=mt(e),r=0,i=o.length;i>r;r++)yt(o[r],s[r]);if(t)if(n)for(o=o||mt(e),s=s||mt(a),r=0,i=o.length;i>r;r++)gt(o[r],s[r]);else gt(e,a);return s=mt(a,"script"),s.length>0&&dt(s,!u&&mt(e,"script")),a},buildFragment:function(e,t,n,r){var i,o,s,a,u,l,c=0,p=e.length,f=t.createDocumentFragment(),h=[];for(;p>c;c++)if(i=e[c],i||0===i)if("object"===x.type(i))x.merge(h,i.nodeType?[i]:i);else if(rt.test(i)){o=o||f.appendChild(t.createElement("div")),s=(nt.exec(i)||["",""])[1].toLowerCase(),a=ct[s]||ct._default,o.innerHTML=a[1]+i.replace(tt,"<$1></$2>")+a[2],l=a[0];while(l--)o=o.lastChild;x.merge(h,o.childNodes),o=f.firstChild,o.textContent=""}else h.push(t.createTextNode(i));f.textContent="",c=0;while(i=h[c++])if((!r||-1===x.inArray(i,r))&&(u=x.contains(i.ownerDocument,i),o=mt(f.appendChild(i),"script"),u&&dt(o),n)){l=0;while(i=o[l++])at.test(i.type||"")&&n.push(i)}return f},cleanData:function(e){var t,n,r,i,o,s,a=x.event.special,u=0;for(;(n=e[u])!==undefined;u++){if(F.accepts(n)&&(o=n[q.expando],o&&(t=q.cache[o]))){if(r=Object.keys(t.events||{}),r.length)for(s=0;(i=r[s])!==undefined;s++)a[i]?x.event.remove(n,i):x.removeEvent(n,i,t.handle);q.cache[o]&&delete q.cache[o]}delete L.cache[n[L.expando]]}},_evalUrl:function(e){return x.ajax({url:e,type:"GET",dataType:"script",async:!1,global:!1,"throws":!0})}});function pt(e,t){return x.nodeName(e,"table")&&x.nodeName(1===t.nodeType?t:t.firstChild,"tr")?e.getElementsByTagName("tbody")[0]||e.appendChild(e.ownerDocument.createElement("tbody")):e}function ft(e){return e.type=(null!==e.getAttribute("type"))+"/"+e.type,e}function ht(e){var t=ut.exec(e.type);return t?e.type=t[1]:e.removeAttribute("type"),e}function dt(e,t){var n=e.length,r=0;for(;n>r;r++)q.set(e[r],"globalEval",!t||q.get(t[r],"globalEval"))}function gt(e,t){var n,r,i,o,s,a,u,l;if(1===t.nodeType){if(q.hasData(e)&&(o=q.access(e),s=q.set(t,o),l=o.events)){delete s.handle,s.events={};for(i in l)for(n=0,r=l[i].length;r>n;n++)x.event.add(t,i,l[i][n])}L.hasData(e)&&(a=L.access(e),u=x.extend({},a),L.set(t,u))}}function mt(e,t){var n=e.getElementsByTagName?e.getElementsByTagName(t||"*"):e.querySelectorAll?e.querySelectorAll(t||"*"):[];return t===undefined||t&&x.nodeName(e,t)?x.merge([e],n):n}function yt(e,t){var n=t.nodeName.toLowerCase();"input"===n&&ot.test(e.type)?t.checked=e.checked:("input"===n||"textarea"===n)&&(t.defaultValue=e.defaultValue)}x.fn.extend({wrapAll:function(e){var t;return x.isFunction(e)?this.each(function(t){x(this).wrapAll(e.call(this,t))}):(this[0]&&(t=x(e,this[0].ownerDocument).eq(0).clone(!0),this[0].parentNode&&t.insertBefore(this[0]),t.map(function(){var e=this;while(e.firstElementChild)e=e.firstElementChild;return e}).append(this)),this)},wrapInner:function(e){return x.isFunction(e)?this.each(function(t){x(this).wrapInner(e.call(this,t))}):this.each(function(){var t=x(this),n=t.contents();n.length?n.wrapAll(e):t.append(e)})},wrap:function(e){var t=x.isFunction(e);return this.each(function(n){x(this).wrapAll(t?e.call(this,n):e)})},unwrap:function(){return this.parent().each(function(){x.nodeName(this,"body")||x(this).replaceWith(this.childNodes)}).end()}});var vt,xt,bt=/^(none|table(?!-c[ea]).+)/,wt=/^margin/,Tt=RegExp("^("+b+")(.*)$","i"),Ct=RegExp("^("+b+")(?!px)[a-z%]+$","i"),kt=RegExp("^([+-])=("+b+")","i"),Nt={BODY:"block"},Et={position:"absolute",visibility:"hidden",display:"block"},St={letterSpacing:0,fontWeight:400},jt=["Top","Right","Bottom","Left"],Dt=["Webkit","O","Moz","ms"];function At(e,t){if(t in e)return t;var n=t.charAt(0).toUpperCase()+t.slice(1),r=t,i=Dt.length;while(i--)if(t=Dt[i]+n,t in e)return t;return r}function Lt(e,t){return e=t||e,"none"===x.css(e,"display")||!x.contains(e.ownerDocument,e)}function qt(t){return e.getComputedStyle(t,null)}function Ht(e,t){var n,r,i,o=[],s=0,a=e.length;for(;a>s;s++)r=e[s],r.style&&(o[s]=q.get(r,"olddisplay"),n=r.style.display,t?(o[s]||"none"!==n||(r.style.display=""),""===r.style.display&&Lt(r)&&(o[s]=q.access(r,"olddisplay",Rt(r.nodeName)))):o[s]||(i=Lt(r),(n&&"none"!==n||!i)&&q.set(r,"olddisplay",i?n:x.css(r,"display"))));for(s=0;a>s;s++)r=e[s],r.style&&(t&&"none"!==r.style.display&&""!==r.style.display||(r.style.display=t?o[s]||"":"none"));return e}x.fn.extend({css:function(e,t){return x.access(this,function(e,t,n){var r,i,o={},s=0;if(x.isArray(t)){for(r=qt(e),i=t.length;i>s;s++)o[t[s]]=x.css(e,t[s],!1,r);return o}return n!==undefined?x.style(e,t,n):x.css(e,t)},e,t,arguments.length>1)},show:function(){return Ht(this,!0)},hide:function(){return Ht(this)},toggle:function(e){return"boolean"==typeof e?e?this.show():this.hide():this.each(function(){Lt(this)?x(this).show():x(this).hide()})}}),x.extend({cssHooks:{opacity:{get:function(e,t){if(t){var n=vt(e,"opacity");return""===n?"1":n}}}},cssNumber:{columnCount:!0,fillOpacity:!0,fontWeight:!0,lineHeight:!0,opacity:!0,order:!0,orphans:!0,widows:!0,zIndex:!0,zoom:!0},cssProps:{"float":"cssFloat"},style:function(e,t,n,r){if(e&&3!==e.nodeType&&8!==e.nodeType&&e.style){var i,o,s,a=x.camelCase(t),u=e.style;return t=x.cssProps[a]||(x.cssProps[a]=At(u,a)),s=x.cssHooks[t]||x.cssHooks[a],n===undefined?s&&"get"in s&&(i=s.get(e,!1,r))!==undefined?i:u[t]:(o=typeof n,"string"===o&&(i=kt.exec(n))&&(n=(i[1]+1)*i[2]+parseFloat(x.css(e,t)),o="number"),null==n||"number"===o&&isNaN(n)||("number"!==o||x.cssNumber[a]||(n+="px"),x.support.clearCloneStyle||""!==n||0!==t.indexOf("background")||(u[t]="inherit"),s&&"set"in s&&(n=s.set(e,n,r))===undefined||(u[t]=n)),undefined)}},css:function(e,t,n,r){var i,o,s,a=x.camelCase(t);return t=x.cssProps[a]||(x.cssProps[a]=At(e.style,a)),s=x.cssHooks[t]||x.cssHooks[a],s&&"get"in s&&(i=s.get(e,!0,n)),i===undefined&&(i=vt(e,t,r)),"normal"===i&&t in St&&(i=St[t]),""===n||n?(o=parseFloat(i),n===!0||x.isNumeric(o)?o||0:i):i}}),vt=function(e,t,n){var r,i,o,s=n||qt(e),a=s?s.getPropertyValue(t)||s[t]:undefined,u=e.style;return s&&(""!==a||x.contains(e.ownerDocument,e)||(a=x.style(e,t)),Ct.test(a)&&wt.test(t)&&(r=u.width,i=u.minWidth,o=u.maxWidth,u.minWidth=u.maxWidth=u.width=a,a=s.width,u.width=r,u.minWidth=i,u.maxWidth=o)),a};function Ot(e,t,n){var r=Tt.exec(t);return r?Math.max(0,r[1]-(n||0))+(r[2]||"px"):t}function Ft(e,t,n,r,i){var o=n===(r?"border":"content")?4:"width"===t?1:0,s=0;for(;4>o;o+=2)"margin"===n&&(s+=x.css(e,n+jt[o],!0,i)),r?("content"===n&&(s-=x.css(e,"padding"+jt[o],!0,i)),"margin"!==n&&(s-=x.css(e,"border"+jt[o]+"Width",!0,i))):(s+=x.css(e,"padding"+jt[o],!0,i),"padding"!==n&&(s+=x.css(e,"border"+jt[o]+"Width",!0,i)));return s}function Pt(e,t,n){var r=!0,i="width"===t?e.offsetWidth:e.offsetHeight,o=qt(e),s=x.support.boxSizing&&"border-box"===x.css(e,"boxSizing",!1,o);if(0>=i||null==i){if(i=vt(e,t,o),(0>i||null==i)&&(i=e.style[t]),Ct.test(i))return i;r=s&&(x.support.boxSizingReliable||i===e.style[t]),i=parseFloat(i)||0}return i+Ft(e,t,n||(s?"border":"content"),r,o)+"px"}function Rt(e){var t=o,n=Nt[e];return n||(n=Mt(e,t),"none"!==n&&n||(xt=(xt||x("<iframe frameborder='0' width='0' height='0'/>").css("cssText","display:block !important")).appendTo(t.documentElement),t=(xt[0].contentWindow||xt[0].contentDocument).document,t.write("<!doctype html><html><body>"),t.close(),n=Mt(e,t),xt.detach()),Nt[e]=n),n}function Mt(e,t){var n=x(t.createElement(e)).appendTo(t.body),r=x.css(n[0],"display");return n.remove(),r}x.each(["height","width"],function(e,t){x.cssHooks[t]={get:function(e,n,r){return n?0===e.offsetWidth&&bt.test(x.css(e,"display"))?x.swap(e,Et,function(){return Pt(e,t,r)}):Pt(e,t,r):undefined},set:function(e,n,r){var i=r&&qt(e);return Ot(e,n,r?Ft(e,t,r,x.support.boxSizing&&"border-box"===x.css(e,"boxSizing",!1,i),i):0)}}}),x(function(){x.support.reliableMarginRight||(x.cssHooks.marginRight={get:function(e,t){return t?x.swap(e,{display:"inline-block"},vt,[e,"marginRight"]):undefined}}),!x.support.pixelPosition&&x.fn.position&&x.each(["top","left"],function(e,t){x.cssHooks[t]={get:function(e,n){return n?(n=vt(e,t),Ct.test(n)?x(e).position()[t]+"px":n):undefined}}})}),x.expr&&x.expr.filters&&(x.expr.filters.hidden=function(e){return 0>=e.offsetWidth&&0>=e.offsetHeight},x.expr.filters.visible=function(e){return!x.expr.filters.hidden(e)}),x.each({margin:"",padding:"",border:"Width"},function(e,t){x.cssHooks[e+t]={expand:function(n){var r=0,i={},o="string"==typeof n?n.split(" "):[n];for(;4>r;r++)i[e+jt[r]+t]=o[r]||o[r-2]||o[0];return i}},wt.test(e)||(x.cssHooks[e+t].set=Ot)});var Wt=/%20/g,$t=/\[\]$/,Bt=/\r?\n/g,It=/^(?:submit|button|image|reset|file)$/i,zt=/^(?:input|select|textarea|keygen)/i;x.fn.extend({serialize:function(){return x.param(this.serializeArray())},serializeArray:function(){return this.map(function(){var e=x.prop(this,"elements");return e?x.makeArray(e):this}).filter(function(){var e=this.type;return this.name&&!x(this).is(":disabled")&&zt.test(this.nodeName)&&!It.test(e)&&(this.checked||!ot.test(e))}).map(function(e,t){var n=x(this).val();return null==n?null:x.isArray(n)?x.map(n,function(e){return{name:t.name,value:e.replace(Bt,"\r\n")}}):{name:t.name,value:n.replace(Bt,"\r\n")}}).get()}}),x.param=function(e,t){var n,r=[],i=function(e,t){t=x.isFunction(t)?t():null==t?"":t,r[r.length]=encodeURIComponent(e)+"="+encodeURIComponent(t)};if(t===undefined&&(t=x.ajaxSettings&&x.ajaxSettings.traditional),x.isArray(e)||e.jquery&&!x.isPlainObject(e))x.each(e,function(){i(this.name,this.value)});else for(n in e)_t(n,e[n],t,i);return r.join("&").replace(Wt,"+")};function _t(e,t,n,r){var i;if(x.isArray(t))x.each(t,function(t,i){n||$t.test(e)?r(e,i):_t(e+"["+("object"==typeof i?t:"")+"]",i,n,r)});else if(n||"object"!==x.type(t))r(e,t);else for(i in t)_t(e+"["+i+"]",t[i],n,r)}x.each("blur focus focusin focusout load resize scroll unload click dblclick mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave change select submit keydown keypress keyup error contextmenu".split(" "),function(e,t){x.fn[t]=function(e,n){return arguments.length>0?this.on(t,null,e,n):this.trigger(t)}}),x.fn.extend({hover:function(e,t){return this.mouseenter(e).mouseleave(t||e)},bind:function(e,t,n){return this.on(e,null,t,n)},unbind:function(e,t){return this.off(e,null,t)
},delegate:function(e,t,n,r){return this.on(t,e,n,r)},undelegate:function(e,t,n){return 1===arguments.length?this.off(e,"**"):this.off(t,e||"**",n)}});var Xt,Ut,Yt=x.now(),Vt=/\?/,Gt=/#.*$/,Jt=/([?&])_=[^&]*/,Qt=/^(.*?):[ \t]*([^\r\n]*)$/gm,Kt=/^(?:about|app|app-storage|.+-extension|file|res|widget):$/,Zt=/^(?:GET|HEAD)$/,en=/^\/\//,tn=/^([\w.+-]+:)(?:\/\/([^\/?#:]*)(?::(\d+)|)|)/,nn=x.fn.load,rn={},on={},sn="*/".concat("*");try{Ut=i.href}catch(an){Ut=o.createElement("a"),Ut.href="",Ut=Ut.href}Xt=tn.exec(Ut.toLowerCase())||[];function un(e){return function(t,n){"string"!=typeof t&&(n=t,t="*");var r,i=0,o=t.toLowerCase().match(w)||[];if(x.isFunction(n))while(r=o[i++])"+"===r[0]?(r=r.slice(1)||"*",(e[r]=e[r]||[]).unshift(n)):(e[r]=e[r]||[]).push(n)}}function ln(e,t,n,r){var i={},o=e===on;function s(a){var u;return i[a]=!0,x.each(e[a]||[],function(e,a){var l=a(t,n,r);return"string"!=typeof l||o||i[l]?o?!(u=l):undefined:(t.dataTypes.unshift(l),s(l),!1)}),u}return s(t.dataTypes[0])||!i["*"]&&s("*")}function cn(e,t){var n,r,i=x.ajaxSettings.flatOptions||{};for(n in t)t[n]!==undefined&&((i[n]?e:r||(r={}))[n]=t[n]);return r&&x.extend(!0,e,r),e}x.fn.load=function(e,t,n){if("string"!=typeof e&&nn)return nn.apply(this,arguments);var r,i,o,s=this,a=e.indexOf(" ");return a>=0&&(r=e.slice(a),e=e.slice(0,a)),x.isFunction(t)?(n=t,t=undefined):t&&"object"==typeof t&&(i="POST"),s.length>0&&x.ajax({url:e,type:i,dataType:"html",data:t}).done(function(e){o=arguments,s.html(r?x("<div>").append(x.parseHTML(e)).find(r):e)}).complete(n&&function(e,t){s.each(n,o||[e.responseText,t,e])}),this},x.each(["ajaxStart","ajaxStop","ajaxComplete","ajaxError","ajaxSuccess","ajaxSend"],function(e,t){x.fn[t]=function(e){return this.on(t,e)}}),x.extend({active:0,lastModified:{},etag:{},ajaxSettings:{url:Ut,type:"GET",isLocal:Kt.test(Xt[1]),global:!0,processData:!0,async:!0,contentType:"application/x-www-form-urlencoded; charset=UTF-8",accepts:{"*":sn,text:"text/plain",html:"text/html",xml:"application/xml, text/xml",json:"application/json, text/javascript"},contents:{xml:/xml/,html:/html/,json:/json/},responseFields:{xml:"responseXML",text:"responseText",json:"responseJSON"},converters:{"* text":String,"text html":!0,"text json":x.parseJSON,"text xml":x.parseXML},flatOptions:{url:!0,context:!0}},ajaxSetup:function(e,t){return t?cn(cn(e,x.ajaxSettings),t):cn(x.ajaxSettings,e)},ajaxPrefilter:un(rn),ajaxTransport:un(on),ajax:function(e,t){"object"==typeof e&&(t=e,e=undefined),t=t||{};var n,r,i,o,s,a,u,l,c=x.ajaxSetup({},t),p=c.context||c,f=c.context&&(p.nodeType||p.jquery)?x(p):x.event,h=x.Deferred(),d=x.Callbacks("once memory"),g=c.statusCode||{},m={},y={},v=0,b="canceled",T={readyState:0,getResponseHeader:function(e){var t;if(2===v){if(!o){o={};while(t=Qt.exec(i))o[t[1].toLowerCase()]=t[2]}t=o[e.toLowerCase()]}return null==t?null:t},getAllResponseHeaders:function(){return 2===v?i:null},setRequestHeader:function(e,t){var n=e.toLowerCase();return v||(e=y[n]=y[n]||e,m[e]=t),this},overrideMimeType:function(e){return v||(c.mimeType=e),this},statusCode:function(e){var t;if(e)if(2>v)for(t in e)g[t]=[g[t],e[t]];else T.always(e[T.status]);return this},abort:function(e){var t=e||b;return n&&n.abort(t),k(0,t),this}};if(h.promise(T).complete=d.add,T.success=T.done,T.error=T.fail,c.url=((e||c.url||Ut)+"").replace(Gt,"").replace(en,Xt[1]+"//"),c.type=t.method||t.type||c.method||c.type,c.dataTypes=x.trim(c.dataType||"*").toLowerCase().match(w)||[""],null==c.crossDomain&&(a=tn.exec(c.url.toLowerCase()),c.crossDomain=!(!a||a[1]===Xt[1]&&a[2]===Xt[2]&&(a[3]||("http:"===a[1]?"80":"443"))===(Xt[3]||("http:"===Xt[1]?"80":"443")))),c.data&&c.processData&&"string"!=typeof c.data&&(c.data=x.param(c.data,c.traditional)),ln(rn,c,t,T),2===v)return T;u=c.global,u&&0===x.active++&&x.event.trigger("ajaxStart"),c.type=c.type.toUpperCase(),c.hasContent=!Zt.test(c.type),r=c.url,c.hasContent||(c.data&&(r=c.url+=(Vt.test(r)?"&":"?")+c.data,delete c.data),c.cache===!1&&(c.url=Jt.test(r)?r.replace(Jt,"$1_="+Yt++):r+(Vt.test(r)?"&":"?")+"_="+Yt++)),c.ifModified&&(x.lastModified[r]&&T.setRequestHeader("If-Modified-Since",x.lastModified[r]),x.etag[r]&&T.setRequestHeader("If-None-Match",x.etag[r])),(c.data&&c.hasContent&&c.contentType!==!1||t.contentType)&&T.setRequestHeader("Content-Type",c.contentType),T.setRequestHeader("Accept",c.dataTypes[0]&&c.accepts[c.dataTypes[0]]?c.accepts[c.dataTypes[0]]+("*"!==c.dataTypes[0]?", "+sn+"; q=0.01":""):c.accepts["*"]);for(l in c.headers)T.setRequestHeader(l,c.headers[l]);if(c.beforeSend&&(c.beforeSend.call(p,T,c)===!1||2===v))return T.abort();b="abort";for(l in{success:1,error:1,complete:1})T[l](c[l]);if(n=ln(on,c,t,T)){T.readyState=1,u&&f.trigger("ajaxSend",[T,c]),c.async&&c.timeout>0&&(s=setTimeout(function(){T.abort("timeout")},c.timeout));try{v=1,n.send(m,k)}catch(C){if(!(2>v))throw C;k(-1,C)}}else k(-1,"No Transport");function k(e,t,o,a){var l,m,y,b,w,C=t;2!==v&&(v=2,s&&clearTimeout(s),n=undefined,i=a||"",T.readyState=e>0?4:0,l=e>=200&&300>e||304===e,o&&(b=pn(c,T,o)),b=fn(c,b,T,l),l?(c.ifModified&&(w=T.getResponseHeader("Last-Modified"),w&&(x.lastModified[r]=w),w=T.getResponseHeader("etag"),w&&(x.etag[r]=w)),204===e||"HEAD"===c.type?C="nocontent":304===e?C="notmodified":(C=b.state,m=b.data,y=b.error,l=!y)):(y=C,(e||!C)&&(C="error",0>e&&(e=0))),T.status=e,T.statusText=(t||C)+"",l?h.resolveWith(p,[m,C,T]):h.rejectWith(p,[T,C,y]),T.statusCode(g),g=undefined,u&&f.trigger(l?"ajaxSuccess":"ajaxError",[T,c,l?m:y]),d.fireWith(p,[T,C]),u&&(f.trigger("ajaxComplete",[T,c]),--x.active||x.event.trigger("ajaxStop")))}return T},getJSON:function(e,t,n){return x.get(e,t,n,"json")},getScript:function(e,t){return x.get(e,undefined,t,"script")}}),x.each(["get","post"],function(e,t){x[t]=function(e,n,r,i){return x.isFunction(n)&&(i=i||r,r=n,n=undefined),x.ajax({url:e,type:t,dataType:i,data:n,success:r})}});function pn(e,t,n){var r,i,o,s,a=e.contents,u=e.dataTypes;while("*"===u[0])u.shift(),r===undefined&&(r=e.mimeType||t.getResponseHeader("Content-Type"));if(r)for(i in a)if(a[i]&&a[i].test(r)){u.unshift(i);break}if(u[0]in n)o=u[0];else{for(i in n){if(!u[0]||e.converters[i+" "+u[0]]){o=i;break}s||(s=i)}o=o||s}return o?(o!==u[0]&&u.unshift(o),n[o]):undefined}function fn(e,t,n,r){var i,o,s,a,u,l={},c=e.dataTypes.slice();if(c[1])for(s in e.converters)l[s.toLowerCase()]=e.converters[s];o=c.shift();while(o)if(e.responseFields[o]&&(n[e.responseFields[o]]=t),!u&&r&&e.dataFilter&&(t=e.dataFilter(t,e.dataType)),u=o,o=c.shift())if("*"===o)o=u;else if("*"!==u&&u!==o){if(s=l[u+" "+o]||l["* "+o],!s)for(i in l)if(a=i.split(" "),a[1]===o&&(s=l[u+" "+a[0]]||l["* "+a[0]])){s===!0?s=l[i]:l[i]!==!0&&(o=a[0],c.unshift(a[1]));break}if(s!==!0)if(s&&e["throws"])t=s(t);else try{t=s(t)}catch(p){return{state:"parsererror",error:s?p:"No conversion from "+u+" to "+o}}}return{state:"success",data:t}}x.ajaxSetup({accepts:{script:"text/javascript, application/javascript, application/ecmascript, application/x-ecmascript"},contents:{script:/(?:java|ecma)script/},converters:{"text script":function(e){return x.globalEval(e),e}}}),x.ajaxPrefilter("script",function(e){e.cache===undefined&&(e.cache=!1),e.crossDomain&&(e.type="GET")}),x.ajaxTransport("script",function(e){if(e.crossDomain){var t,n;return{send:function(r,i){t=x("<script>").prop({async:!0,charset:e.scriptCharset,src:e.url}).on("load error",n=function(e){t.remove(),n=null,e&&i("error"===e.type?404:200,e.type)}),o.head.appendChild(t[0])},abort:function(){n&&n()}}}});var hn=[],dn=/(=)\?(?=&|$)|\?\?/;x.ajaxSetup({jsonp:"callback",jsonpCallback:function(){var e=hn.pop()||x.expando+"_"+Yt++;return this[e]=!0,e}}),x.ajaxPrefilter("json jsonp",function(t,n,r){var i,o,s,a=t.jsonp!==!1&&(dn.test(t.url)?"url":"string"==typeof t.data&&!(t.contentType||"").indexOf("application/x-www-form-urlencoded")&&dn.test(t.data)&&"data");return a||"jsonp"===t.dataTypes[0]?(i=t.jsonpCallback=x.isFunction(t.jsonpCallback)?t.jsonpCallback():t.jsonpCallback,a?t[a]=t[a].replace(dn,"$1"+i):t.jsonp!==!1&&(t.url+=(Vt.test(t.url)?"&":"?")+t.jsonp+"="+i),t.converters["script json"]=function(){return s||x.error(i+" was not called"),s[0]},t.dataTypes[0]="json",o=e[i],e[i]=function(){s=arguments},r.always(function(){e[i]=o,t[i]&&(t.jsonpCallback=n.jsonpCallback,hn.push(i)),s&&x.isFunction(o)&&o(s[0]),s=o=undefined}),"script"):undefined}),x.ajaxSettings.xhr=function(){try{return new XMLHttpRequest}catch(e){}};var gn=x.ajaxSettings.xhr(),mn={0:200,1223:204},yn=0,vn={};e.ActiveXObject&&x(e).on("unload",function(){for(var e in vn)vn[e]();vn=undefined}),x.support.cors=!!gn&&"withCredentials"in gn,x.support.ajax=gn=!!gn,x.ajaxTransport(function(e){var t;return x.support.cors||gn&&!e.crossDomain?{send:function(n,r){var i,o,s=e.xhr();if(s.open(e.type,e.url,e.async,e.username,e.password),e.xhrFields)for(i in e.xhrFields)s[i]=e.xhrFields[i];e.mimeType&&s.overrideMimeType&&s.overrideMimeType(e.mimeType),e.crossDomain||n["X-Requested-With"]||(n["X-Requested-With"]="XMLHttpRequest");for(i in n)s.setRequestHeader(i,n[i]);t=function(e){return function(){t&&(delete vn[o],t=s.onload=s.onerror=null,"abort"===e?s.abort():"error"===e?r(s.status||404,s.statusText):r(mn[s.status]||s.status,s.statusText,"string"==typeof s.responseText?{text:s.responseText}:undefined,s.getAllResponseHeaders()))}},s.onload=t(),s.onerror=t("error"),t=vn[o=yn++]=t("abort"),s.send(e.hasContent&&e.data||null)},abort:function(){t&&t()}}:undefined});var xn,bn,wn=/^(?:toggle|show|hide)$/,Tn=RegExp("^(?:([+-])=|)("+b+")([a-z%]*)$","i"),Cn=/queueHooks$/,kn=[An],Nn={"*":[function(e,t){var n=this.createTween(e,t),r=n.cur(),i=Tn.exec(t),o=i&&i[3]||(x.cssNumber[e]?"":"px"),s=(x.cssNumber[e]||"px"!==o&&+r)&&Tn.exec(x.css(n.elem,e)),a=1,u=20;if(s&&s[3]!==o){o=o||s[3],i=i||[],s=+r||1;do a=a||".5",s/=a,x.style(n.elem,e,s+o);while(a!==(a=n.cur()/r)&&1!==a&&--u)}return i&&(s=n.start=+s||+r||0,n.unit=o,n.end=i[1]?s+(i[1]+1)*i[2]:+i[2]),n}]};function En(){return setTimeout(function(){xn=undefined}),xn=x.now()}function Sn(e,t,n){var r,i=(Nn[t]||[]).concat(Nn["*"]),o=0,s=i.length;for(;s>o;o++)if(r=i[o].call(n,t,e))return r}function jn(e,t,n){var r,i,o=0,s=kn.length,a=x.Deferred().always(function(){delete u.elem}),u=function(){if(i)return!1;var t=xn||En(),n=Math.max(0,l.startTime+l.duration-t),r=n/l.duration||0,o=1-r,s=0,u=l.tweens.length;for(;u>s;s++)l.tweens[s].run(o);return a.notifyWith(e,[l,o,n]),1>o&&u?n:(a.resolveWith(e,[l]),!1)},l=a.promise({elem:e,props:x.extend({},t),opts:x.extend(!0,{specialEasing:{}},n),originalProperties:t,originalOptions:n,startTime:xn||En(),duration:n.duration,tweens:[],createTween:function(t,n){var r=x.Tween(e,l.opts,t,n,l.opts.specialEasing[t]||l.opts.easing);return l.tweens.push(r),r},stop:function(t){var n=0,r=t?l.tweens.length:0;if(i)return this;for(i=!0;r>n;n++)l.tweens[n].run(1);return t?a.resolveWith(e,[l,t]):a.rejectWith(e,[l,t]),this}}),c=l.props;for(Dn(c,l.opts.specialEasing);s>o;o++)if(r=kn[o].call(l,e,c,l.opts))return r;return x.map(c,Sn,l),x.isFunction(l.opts.start)&&l.opts.start.call(e,l),x.fx.timer(x.extend(u,{elem:e,anim:l,queue:l.opts.queue})),l.progress(l.opts.progress).done(l.opts.done,l.opts.complete).fail(l.opts.fail).always(l.opts.always)}function Dn(e,t){var n,r,i,o,s;for(n in e)if(r=x.camelCase(n),i=t[r],o=e[n],x.isArray(o)&&(i=o[1],o=e[n]=o[0]),n!==r&&(e[r]=o,delete e[n]),s=x.cssHooks[r],s&&"expand"in s){o=s.expand(o),delete e[r];for(n in o)n in e||(e[n]=o[n],t[n]=i)}else t[r]=i}x.Animation=x.extend(jn,{tweener:function(e,t){x.isFunction(e)?(t=e,e=["*"]):e=e.split(" ");var n,r=0,i=e.length;for(;i>r;r++)n=e[r],Nn[n]=Nn[n]||[],Nn[n].unshift(t)},prefilter:function(e,t){t?kn.unshift(e):kn.push(e)}});function An(e,t,n){var r,i,o,s,a,u,l=this,c={},p=e.style,f=e.nodeType&&Lt(e),h=q.get(e,"fxshow");n.queue||(a=x._queueHooks(e,"fx"),null==a.unqueued&&(a.unqueued=0,u=a.empty.fire,a.empty.fire=function(){a.unqueued||u()}),a.unqueued++,l.always(function(){l.always(function(){a.unqueued--,x.queue(e,"fx").length||a.empty.fire()})})),1===e.nodeType&&("height"in t||"width"in t)&&(n.overflow=[p.overflow,p.overflowX,p.overflowY],"inline"===x.css(e,"display")&&"none"===x.css(e,"float")&&(p.display="inline-block")),n.overflow&&(p.overflow="hidden",l.always(function(){p.overflow=n.overflow[0],p.overflowX=n.overflow[1],p.overflowY=n.overflow[2]}));for(r in t)if(i=t[r],wn.exec(i)){if(delete t[r],o=o||"toggle"===i,i===(f?"hide":"show")){if("show"!==i||!h||h[r]===undefined)continue;f=!0}c[r]=h&&h[r]||x.style(e,r)}if(!x.isEmptyObject(c)){h?"hidden"in h&&(f=h.hidden):h=q.access(e,"fxshow",{}),o&&(h.hidden=!f),f?x(e).show():l.done(function(){x(e).hide()}),l.done(function(){var t;q.remove(e,"fxshow");for(t in c)x.style(e,t,c[t])});for(r in c)s=Sn(f?h[r]:0,r,l),r in h||(h[r]=s.start,f&&(s.end=s.start,s.start="width"===r||"height"===r?1:0))}}function Ln(e,t,n,r,i){return new Ln.prototype.init(e,t,n,r,i)}x.Tween=Ln,Ln.prototype={constructor:Ln,init:function(e,t,n,r,i,o){this.elem=e,this.prop=n,this.easing=i||"swing",this.options=t,this.start=this.now=this.cur(),this.end=r,this.unit=o||(x.cssNumber[n]?"":"px")},cur:function(){var e=Ln.propHooks[this.prop];return e&&e.get?e.get(this):Ln.propHooks._default.get(this)},run:function(e){var t,n=Ln.propHooks[this.prop];return this.pos=t=this.options.duration?x.easing[this.easing](e,this.options.duration*e,0,1,this.options.duration):e,this.now=(this.end-this.start)*t+this.start,this.options.step&&this.options.step.call(this.elem,this.now,this),n&&n.set?n.set(this):Ln.propHooks._default.set(this),this}},Ln.prototype.init.prototype=Ln.prototype,Ln.propHooks={_default:{get:function(e){var t;return null==e.elem[e.prop]||e.elem.style&&null!=e.elem.style[e.prop]?(t=x.css(e.elem,e.prop,""),t&&"auto"!==t?t:0):e.elem[e.prop]},set:function(e){x.fx.step[e.prop]?x.fx.step[e.prop](e):e.elem.style&&(null!=e.elem.style[x.cssProps[e.prop]]||x.cssHooks[e.prop])?x.style(e.elem,e.prop,e.now+e.unit):e.elem[e.prop]=e.now}}},Ln.propHooks.scrollTop=Ln.propHooks.scrollLeft={set:function(e){e.elem.nodeType&&e.elem.parentNode&&(e.elem[e.prop]=e.now)}},x.each(["toggle","show","hide"],function(e,t){var n=x.fn[t];x.fn[t]=function(e,r,i){return null==e||"boolean"==typeof e?n.apply(this,arguments):this.animate(qn(t,!0),e,r,i)}}),x.fn.extend({fadeTo:function(e,t,n,r){return this.filter(Lt).css("opacity",0).show().end().animate({opacity:t},e,n,r)},animate:function(e,t,n,r){var i=x.isEmptyObject(e),o=x.speed(t,n,r),s=function(){var t=jn(this,x.extend({},e),o);(i||q.get(this,"finish"))&&t.stop(!0)};return s.finish=s,i||o.queue===!1?this.each(s):this.queue(o.queue,s)},stop:function(e,t,n){var r=function(e){var t=e.stop;delete e.stop,t(n)};return"string"!=typeof e&&(n=t,t=e,e=undefined),t&&e!==!1&&this.queue(e||"fx",[]),this.each(function(){var t=!0,i=null!=e&&e+"queueHooks",o=x.timers,s=q.get(this);if(i)s[i]&&s[i].stop&&r(s[i]);else for(i in s)s[i]&&s[i].stop&&Cn.test(i)&&r(s[i]);for(i=o.length;i--;)o[i].elem!==this||null!=e&&o[i].queue!==e||(o[i].anim.stop(n),t=!1,o.splice(i,1));(t||!n)&&x.dequeue(this,e)})},finish:function(e){return e!==!1&&(e=e||"fx"),this.each(function(){var t,n=q.get(this),r=n[e+"queue"],i=n[e+"queueHooks"],o=x.timers,s=r?r.length:0;for(n.finish=!0,x.queue(this,e,[]),i&&i.stop&&i.stop.call(this,!0),t=o.length;t--;)o[t].elem===this&&o[t].queue===e&&(o[t].anim.stop(!0),o.splice(t,1));for(t=0;s>t;t++)r[t]&&r[t].finish&&r[t].finish.call(this);delete n.finish})}});function qn(e,t){var n,r={height:e},i=0;for(t=t?1:0;4>i;i+=2-t)n=jt[i],r["margin"+n]=r["padding"+n]=e;return t&&(r.opacity=r.width=e),r}x.each({slideDown:qn("show"),slideUp:qn("hide"),slideToggle:qn("toggle"),fadeIn:{opacity:"show"},fadeOut:{opacity:"hide"},fadeToggle:{opacity:"toggle"}},function(e,t){x.fn[e]=function(e,n,r){return this.animate(t,e,n,r)}}),x.speed=function(e,t,n){var r=e&&"object"==typeof e?x.extend({},e):{complete:n||!n&&t||x.isFunction(e)&&e,duration:e,easing:n&&t||t&&!x.isFunction(t)&&t};return r.duration=x.fx.off?0:"number"==typeof r.duration?r.duration:r.duration in x.fx.speeds?x.fx.speeds[r.duration]:x.fx.speeds._default,(null==r.queue||r.queue===!0)&&(r.queue="fx"),r.old=r.complete,r.complete=function(){x.isFunction(r.old)&&r.old.call(this),r.queue&&x.dequeue(this,r.queue)},r},x.easing={linear:function(e){return e},swing:function(e){return.5-Math.cos(e*Math.PI)/2}},x.timers=[],x.fx=Ln.prototype.init,x.fx.tick=function(){var e,t=x.timers,n=0;for(xn=x.now();t.length>n;n++)e=t[n],e()||t[n]!==e||t.splice(n--,1);t.length||x.fx.stop(),xn=undefined},x.fx.timer=function(e){e()&&x.timers.push(e)&&x.fx.start()},x.fx.interval=13,x.fx.start=function(){bn||(bn=setInterval(x.fx.tick,x.fx.interval))},x.fx.stop=function(){clearInterval(bn),bn=null},x.fx.speeds={slow:600,fast:200,_default:400},x.fx.step={},x.expr&&x.expr.filters&&(x.expr.filters.animated=function(e){return x.grep(x.timers,function(t){return e===t.elem}).length}),x.fn.offset=function(e){if(arguments.length)return e===undefined?this:this.each(function(t){x.offset.setOffset(this,e,t)});var t,n,i=this[0],o={top:0,left:0},s=i&&i.ownerDocument;if(s)return t=s.documentElement,x.contains(t,i)?(typeof i.getBoundingClientRect!==r&&(o=i.getBoundingClientRect()),n=Hn(s),{top:o.top+n.pageYOffset-t.clientTop,left:o.left+n.pageXOffset-t.clientLeft}):o},x.offset={setOffset:function(e,t,n){var r,i,o,s,a,u,l,c=x.css(e,"position"),p=x(e),f={};"static"===c&&(e.style.position="relative"),a=p.offset(),o=x.css(e,"top"),u=x.css(e,"left"),l=("absolute"===c||"fixed"===c)&&(o+u).indexOf("auto")>-1,l?(r=p.position(),s=r.top,i=r.left):(s=parseFloat(o)||0,i=parseFloat(u)||0),x.isFunction(t)&&(t=t.call(e,n,a)),null!=t.top&&(f.top=t.top-a.top+s),null!=t.left&&(f.left=t.left-a.left+i),"using"in t?t.using.call(e,f):p.css(f)}},x.fn.extend({position:function(){if(this[0]){var e,t,n=this[0],r={top:0,left:0};return"fixed"===x.css(n,"position")?t=n.getBoundingClientRect():(e=this.offsetParent(),t=this.offset(),x.nodeName(e[0],"html")||(r=e.offset()),r.top+=x.css(e[0],"borderTopWidth",!0),r.left+=x.css(e[0],"borderLeftWidth",!0)),{top:t.top-r.top-x.css(n,"marginTop",!0),left:t.left-r.left-x.css(n,"marginLeft",!0)}}},offsetParent:function(){return this.map(function(){var e=this.offsetParent||s;while(e&&!x.nodeName(e,"html")&&"static"===x.css(e,"position"))e=e.offsetParent;return e||s})}}),x.each({scrollLeft:"pageXOffset",scrollTop:"pageYOffset"},function(t,n){var r="pageYOffset"===n;x.fn[t]=function(i){return x.access(this,function(t,i,o){var s=Hn(t);return o===undefined?s?s[n]:t[i]:(s?s.scrollTo(r?e.pageXOffset:o,r?o:e.pageYOffset):t[i]=o,undefined)},t,i,arguments.length,null)}});function Hn(e){return x.isWindow(e)?e:9===e.nodeType&&e.defaultView}x.each({Height:"height",Width:"width"},function(e,t){x.each({padding:"inner"+e,content:t,"":"outer"+e},function(n,r){x.fn[r]=function(r,i){var o=arguments.length&&(n||"boolean"!=typeof r),s=n||(r===!0||i===!0?"margin":"border");return x.access(this,function(t,n,r){var i;return x.isWindow(t)?t.document.documentElement["client"+e]:9===t.nodeType?(i=t.documentElement,Math.max(t.body["scroll"+e],i["scroll"+e],t.body["offset"+e],i["offset"+e],i["client"+e])):r===undefined?x.css(t,n,s):x.style(t,n,r,s)},t,o?r:undefined,o,null)}})}),x.fn.size=function(){return this.length},x.fn.andSelf=x.fn.addBack,"object"==typeof module&&module&&"object"==typeof module.exports?module.exports=x:"function"==typeof define&&define.amd&&define("jquery",[],function(){return x}),"object"==typeof e&&"object"==typeof e.document&&(e.jQuery=e.$=x)})(window);

/**
 * @license
 * Lo-Dash 1.3.1 (Custom Build) lodash.com/license
 * Build: `lodash underscore exports="amd,commonjs,global,node" -o ./dist/lodash.underscore.js`
 * Underscore.js 1.4.4 underscorejs.org/LICENSE
 */
;!function(n){function t(n,t){var r;if(n&&gt[typeof n])for(r in n)if(Et.call(n,r)&&t(n[r],r,n)===nt)break}function r(n,t){var r;if(n&&gt[typeof n])for(r in n)if(t(n[r],r,n)===nt)break}function e(n){var t,r=[];if(!n||!gt[typeof n])return r;for(t in n)Et.call(n,t)&&r.push(t);return r}function u(n,t,r){r=(r||0)-1;for(var e=n.length;++r<e;)if(n[r]===t)return r;return-1}function o(n,t){var r=n.m,e=t.m;if(n=n.l,t=t.l,n!==t){if(n>t||typeof n=="undefined")return 1;if(n<t||typeof t=="undefined")return-1}return r<e?-1:1
}function i(n){return"\\"+ht[n]}function a(){}function f(n){return n instanceof f?n:new c(n)}function c(n){this.__wrapped__=n}function l(n,t,r){function e(){var f=arguments,c=o?this:t;return u||(n=t[i]),r.length&&(f=f.length?(f=zt.call(f),a?f.concat(r):r.concat(f)):r),this instanceof e?(c=p(n.prototype),f=n.apply(c,f),A(f)?f:c):n.apply(c,f)}var u=w(n),o=!r,i=t;if(o){var a=void 0;r=t}else if(!u)throw new TypeError;return e}function p(n){return A(n)?Ft(n):{}}function s(n){return Wt[n]}function v(){var n=(n=f.indexOf)===U?u:n;
return n}function g(n){return Gt[n]}function h(n){return kt.call(n)==it}function y(n){if(!n)return n;for(var t=1,r=arguments.length;t<r;t++){var e=arguments[t];if(e)for(var u in e)n[u]=e[u]}return n}function m(n){if(!n)return n;for(var t=1,r=arguments.length;t<r;t++){var e=arguments[t];if(e)for(var u in e)n[u]==X&&(n[u]=e[u])}return n}function _(n){var t=[];return r(n,function(n,r){w(n)&&t.push(r)}),t.sort()}function d(n){for(var t=-1,r=Vt(n),e=r.length,u={};++t<e;){var o=r[t];u[n[o]]=o}return u}function b(n){if(!n)return Q;
if(Ut(n)||O(n))return!n.length;for(var t in n)if(Et.call(n,t))return Y;return Q}function j(n,t,e,u){if(n===t)return 0!==n||1/n==1/t;var o=typeof n,i=typeof t;if(n===n&&(!n||"function"!=o&&"object"!=o)&&(!t||"function"!=i&&"object"!=i))return Y;if(n==X||t==X)return n===t;if(i=kt.call(n),o=kt.call(t),i!=o)return Y;switch(i){case ft:case ct:return+n==+t;case lt:return n!=+n?t!=+t:0==n?1/n==1/t:n==+t;case st:case vt:return n==t+""}if(o=i==at,!o){if(n instanceof f||t instanceof f)return j(n.__wrapped__||n,t.__wrapped__||t,e,u);
if(i!=pt)return Y;var i=n.constructor,a=t.constructor;if(i!=a&&(!w(i)||!(i instanceof i&&w(a)&&a instanceof a)))return Y}for(e||(e=[]),u||(u=[]),i=e.length;i--;)if(e[i]==n)return u[i]==t;var c=Q,l=0;if(e.push(n),u.push(t),o){if(l=t.length,c=l==n.length)for(;l--&&(c=j(n[l],t[l],e,u)););return c}return r(t,function(t,r,o){return Et.call(o,r)?(l++,!(c=Et.call(n,r)&&j(n[r],t,e,u))&&nt):void 0}),c&&r(n,function(n,t,r){return Et.call(r,t)?!(c=-1<--l)&&nt:void 0}),c}function w(n){return typeof n=="function"
}function A(n){return!(!n||!gt[typeof n])}function x(n){return typeof n=="number"||kt.call(n)==lt}function O(n){return typeof n=="string"||kt.call(n)==vt}function E(n){for(var t=-1,r=Vt(n),e=r.length,u=Array(e);++t<e;)u[t]=n[r[t]];return u}function S(n,r){var e=v(),u=n?n.length:0,o=Y;return u&&typeof u=="number"?o=-1<e(n,r):t(n,function(n){return(o=n===r)&&nt}),o}function N(n,r,e){var u=Q;r=J(r,e),e=-1;var o=n?n.length:0;if(typeof o=="number")for(;++e<o&&(u=!!r(n[e],e,n)););else t(n,function(n,t,e){return!(u=!!r(n,t,e))&&nt
});return u}function k(n,r,e){var u=[];r=J(r,e),e=-1;var o=n?n.length:0;if(typeof o=="number")for(;++e<o;){var i=n[e];r(i,e,n)&&u.push(i)}else t(n,function(n,t,e){r(n,t,e)&&u.push(n)});return u}function B(n,r,e){r=J(r,e),e=-1;var u=n?n.length:0;if(typeof u!="number"){var o;return t(n,function(n,t,e){return r(n,t,e)?(o=n,nt):void 0}),o}for(;++e<u;){var i=n[e];if(r(i,e,n))return i}}function F(n,r,e){var u=-1,o=n?n.length:0;if(r=r&&typeof e=="undefined"?r:J(r,e),typeof o=="number")for(;++u<o&&r(n[u],u,n)!==nt;);else t(n,r)
}function q(n,r,e){var u=-1,o=n?n.length:0;if(r=J(r,e),typeof o=="number")for(var i=Array(o);++u<o;)i[u]=r(n[u],u,n);else i=[],t(n,function(n,t,e){i[++u]=r(n,t,e)});return i}function R(n,t,r){var e=-1/0,u=e,o=-1,i=n?n.length:0;if(t||typeof i!="number")t=J(t,r),F(n,function(n,r,o){r=t(n,r,o),r>e&&(e=r,u=n)});else for(;++o<i;)r=n[o],r>u&&(u=r);return u}function D(n,t){var r=-1,e=n?n.length:0;if(typeof e=="number")for(var u=Array(e);++r<e;)u[r]=n[r][t];return u||q(n,t)}function M(n,r,e,u){if(!n)return e;
var o=3>arguments.length;r=J(r,u,4);var i=-1,a=n.length;if(typeof a=="number")for(o&&(e=n[++i]);++i<a;)e=r(e,n[i],i,n);else t(n,function(n,t,u){e=o?(o=Y,n):r(e,n,t,u)});return e}function T(n,t,r,e){var u=n?n.length:0,o=3>arguments.length;if(typeof u!="number")var i=Vt(n),u=i.length;return t=J(t,e,4),F(n,function(e,a,f){a=i?i[--u]:--u,r=o?(o=Y,n[a]):t(r,n[a],a,f)}),r}function $(n,r,e){var u;r=J(r,e),e=-1;var o=n?n.length:0;if(typeof o=="number")for(;++e<o&&!(u=r(n[e],e,n)););else t(n,function(n,t,e){return(u=r(n,t,e))&&nt
});return!!u}function I(n,t,r){return r&&b(t)?X:(r?B:k)(n,t)}function z(n){for(var t=-1,r=v(),e=n.length,u=xt.apply(dt,zt.call(arguments,1)),o=[];++t<e;){var i=n[t];0>r(u,i)&&o.push(i)}return o}function C(n,t,r){if(n){var e=0,u=n.length;if(typeof t!="number"&&t!=X){var o=-1;for(t=J(t,r);++o<u&&t(n[o],o,n);)e++}else if(e=t,e==X||r)return n[0];return zt.call(n,0,$t(Tt(0,e),u))}}function P(n,t){for(var r=-1,e=n?n.length:0,u=[];++r<e;){var o=n[r];Ut(o)?St.apply(u,t?o:P(o)):u.push(o)}return u}function U(n,t,r){if(typeof r=="number"){var e=n?n.length:0;
r=0>r?Tt(0,e+r):r||0}else if(r)return r=W(n,t),n[r]===t?r:-1;return n?u(n,t,r):-1}function V(n,t,r){if(typeof t!="number"&&t!=X){var e=0,u=-1,o=n?n.length:0;for(t=J(t,r);++u<o&&t(n[u],u,n);)e++}else e=t==X||r?1:Tt(0,t);return zt.call(n,e)}function W(n,t,r,e){var u=0,o=n?n.length:u;for(r=r?J(r,e,1):K,t=r(t);u<o;)e=u+o>>>1,r(n[e])<t?u=e+1:o=e;return u}function G(n,t,r,e){var u=-1,o=v(),i=n?n.length:0,a=[],f=a;for(typeof t!="boolean"&&t!=X&&(e=r,r=t,t=Y),r!=X&&(f=[],r=J(r,e));++u<i;){e=n[u];var c=r?r(e,u,n):e;
(t?!u||f[f.length-1]!==c:0>o(f,c))&&(r&&f.push(c),a.push(e))}return a}function H(n,t){return Pt.fastBind||Bt&&2<arguments.length?Bt.call.apply(Bt,arguments):l(n,t,zt.call(arguments,2))}function J(n,t,r){if(n==X)return K;var e=typeof n;if("function"!=e){if("object"!=e)return function(t){return t[n]};var u=Vt(n);return function(t){for(var r=u.length,e=Y;r--&&(e=t[u[r]]===n[u[r]]););return e}}return typeof t=="undefined"?n:1===r?function(r){return n.call(t,r)}:2===r?function(r,e){return n.call(t,r,e)
}:4===r?function(r,e,u,o){return n.call(t,r,e,u,o)}:function(r,e,u){return n.call(t,r,e,u)}}function K(n){return n}function L(n){F(_(n),function(t){var r=f[t]=n[t];f.prototype[t]=function(){var n=[this.__wrapped__];return St.apply(n,arguments),n=r.apply(f,n),this.__chain__&&(n=new c(n),n.__chain__=Q),n}})}var Q=!0,X=null,Y=!1,Z=0,nt={},tt=+new Date+"",rt=/&(?:amp|lt|gt|quot|#39);/g,et=/($^)/,ut=/[&<>"']/g,ot=/['\n\r\t\u2028\u2029\\]/g,it="[object Arguments]",at="[object Array]",ft="[object Boolean]",ct="[object Date]",lt="[object Number]",pt="[object Object]",st="[object RegExp]",vt="[object String]",gt={"boolean":Y,"function":Q,object:Q,number:Y,string:Y,undefined:Y},ht={"\\":"\\","'":"'","\n":"n","\r":"r","\t":"t","\u2028":"u2028","\u2029":"u2029"},yt=gt[typeof exports]&&exports,mt=gt[typeof module]&&module&&module.exports==yt&&module,_t=gt[typeof global]&&global;
!_t||_t.global!==_t&&_t.window!==_t||(n=_t);var dt=[],_t=Object.prototype,bt=n._,jt=RegExp("^"+(_t.valueOf+"").replace(/[.*+?^${}()|[\]\\]/g,"\\$&").replace(/valueOf|for [^\]]+/g,".+?")+"$"),wt=Math.ceil,At=n.clearTimeout,xt=dt.concat,Ot=Math.floor,Et=_t.hasOwnProperty,St=dt.push,Nt=n.setTimeout,kt=_t.toString,Bt=jt.test(Bt=kt.bind)&&Bt,Ft=jt.test(Ft=Object.create)&&Ft,qt=jt.test(qt=Array.isArray)&&qt,Rt=n.isFinite,Dt=n.isNaN,Mt=jt.test(Mt=Object.keys)&&Mt,Tt=Math.max,$t=Math.min,It=Math.random,zt=dt.slice,_t=jt.test(n.attachEvent),Ct=Bt&&!/\n|true/.test(Bt+_t);
c.prototype=f.prototype;var Pt={};!function(){var n={0:1,length:1};Pt.fastBind=Bt&&!Ct,Pt.spliceObjects=(dt.splice.call(n,0,1),!n[0])}(1),f.templateSettings={escape:/<%-([\s\S]+?)%>/g,evaluate:/<%([\s\S]+?)%>/g,interpolate:/<%=([\s\S]+?)%>/g,variable:""},Ft||(p=function(n){if(A(n)){a.prototype=n;var t=new a;a.prototype=X}return t||{}}),h(arguments)||(h=function(n){return n?Et.call(n,"callee"):Y});var Ut=qt||function(n){return n?typeof n=="object"&&kt.call(n)==at:Y},Vt=Mt?function(n){return A(n)?Mt(n):[]
}:e,Wt={"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"},Gt=d(Wt);w(/x/)&&(w=function(n){return typeof n=="function"&&"[object Function]"==kt.call(n)}),f.after=function(n,t){return 1>n?t():function(){return 1>--n?t.apply(this,arguments):void 0}},f.bind=H,f.bindAll=function(n){for(var t=1<arguments.length?xt.apply(dt,zt.call(arguments,1)):_(n),r=-1,e=t.length;++r<e;){var u=t[r];n[u]=H(n[u],n)}return n},f.compact=function(n){for(var t=-1,r=n?n.length:0,e=[];++t<r;){var u=n[t];u&&e.push(u)
}return e},f.compose=function(){var n=arguments;return function(){for(var t=arguments,r=n.length;r--;)t=[n[r].apply(this,t)];return t[0]}},f.countBy=function(n,t,r){var e={};return t=J(t,r),F(n,function(n,r,u){r=t(n,r,u)+"",Et.call(e,r)?e[r]++:e[r]=1}),e},f.debounce=function(n,t,r){function e(){a=X,r||(o=n.apply(i,u))}var u,o,i,a=X;return function(){var f=r&&!a;return u=arguments,i=this,At(a),a=Nt(e,t),f&&(o=n.apply(i,u)),o}},f.defaults=m,f.defer=function(n){var t=zt.call(arguments,1);return Nt(function(){n.apply(void 0,t)
},1)},f.delay=function(n,t){var r=zt.call(arguments,2);return Nt(function(){n.apply(void 0,r)},t)},f.difference=z,f.filter=k,f.flatten=P,f.forEach=F,f.functions=_,f.groupBy=function(n,t,r){var e={};return t=J(t,r),F(n,function(n,r,u){r=t(n,r,u)+"",(Et.call(e,r)?e[r]:e[r]=[]).push(n)}),e},f.initial=function(n,t,r){if(!n)return[];var e=0,u=n.length;if(typeof t!="number"&&t!=X){var o=u;for(t=J(t,r);o--&&t(n[o],o,n);)e++}else e=t==X||r?1:t||e;return zt.call(n,0,$t(Tt(0,u-e),u))},f.intersection=function(n){var t=arguments,r=t.length,e=-1,u=v(),o=n?n.length:0,i=[];
n:for(;++e<o;){var a=n[e];if(0>u(i,a)){for(var f=r;--f;)if(0>u(t[f],a))continue n;i.push(a)}}return i},f.invert=d,f.invoke=function(n,t){var r=zt.call(arguments,2),e=-1,u=typeof t=="function",o=n?n.length:0,i=Array(typeof o=="number"?o:0);return F(n,function(n){i[++e]=(u?t:n[t]).apply(n,r)}),i},f.keys=Vt,f.map=q,f.max=R,f.memoize=function(n,t){var r={};return function(){var e=tt+(t?t.apply(this,arguments):arguments[0]);return Et.call(r,e)?r[e]:r[e]=n.apply(this,arguments)}},f.min=function(n,t,r){var e=1/0,u=e,o=-1,i=n?n.length:0;
if(t||typeof i!="number")t=J(t,r),F(n,function(n,r,o){r=t(n,r,o),r<e&&(e=r,u=n)});else for(;++o<i;)r=n[o],r<u&&(u=r);return u},f.omit=function(n){var t=v(),e=xt.apply(dt,zt.call(arguments,1)),u={};return r(n,function(n,r){0>t(e,r)&&(u[r]=n)}),u},f.once=function(n){var t,r;return function(){return t?r:(t=Q,r=n.apply(this,arguments),n=X,r)}},f.pairs=function(n){for(var t=-1,r=Vt(n),e=r.length,u=Array(e);++t<e;){var o=r[t];u[t]=[o,n[o]]}return u},f.partial=function(n){return l(n,zt.call(arguments,1))
},f.pick=function(n){for(var t=-1,r=xt.apply(dt,zt.call(arguments,1)),e=r.length,u={};++t<e;){var o=r[t];o in n&&(u[o]=n[o])}return u},f.pluck=D,f.range=function(n,t,r){n=+n||0,r=+r||1,t==X&&(t=n,n=0);var e=-1;t=Tt(0,wt((t-n)/r));for(var u=Array(t);++e<t;)u[e]=n,n+=r;return u},f.reject=function(n,t,r){return t=J(t,r),k(n,function(n,r,e){return!t(n,r,e)})},f.rest=V,f.shuffle=function(n){var t=-1,r=n?n.length:0,e=Array(typeof r=="number"?r:0);return F(n,function(n){var r=Ot(It()*(++t+1));e[t]=e[r],e[r]=n
}),e},f.sortBy=function(n,t,r){var e=-1,u=n?n.length:0,i=Array(typeof u=="number"?u:0);for(t=J(t,r),F(n,function(n,r,u){i[++e]={l:t(n,r,u),m:e,n:n}}),u=i.length,i.sort(o);u--;)i[u]=i[u].n;return i},f.tap=function(n,t){return t(n),n},f.throttle=function(n,t){function r(){i=new Date,a=X,u=n.apply(o,e)}var e,u,o,i=0,a=X;return function(){var f=new Date,c=t-(f-i);return e=arguments,o=this,0<c?a||(a=Nt(r,c)):(At(a),a=X,i=f,u=n.apply(o,e)),u}},f.times=function(n,t,r){for(var e=-1,u=Array(-1<n?n:0);++e<n;)u[e]=t.call(r,e);
return u},f.toArray=function(n){return Ut(n)?zt.call(n):n&&typeof n.length=="number"?q(n):E(n)},f.union=function(n){return Ut(n)||(arguments[0]=n?zt.call(n):dt),G(xt.apply(dt,arguments))},f.uniq=G,f.values=E,f.where=I,f.without=function(n){return z(n,zt.call(arguments,1))},f.wrap=function(n,t){return function(){var r=[n];return St.apply(r,arguments),t.apply(this,r)}},f.zip=function(n){for(var t=-1,r=n?R(D(arguments,"length")):0,e=Array(0>r?0:r);++t<r;)e[t]=D(arguments,t);return e},f.collect=q,f.drop=V,f.each=F,f.extend=y,f.methods=_,f.object=function(n,t){for(var r=-1,e=n?n.length:0,u={};++r<e;){var o=n[r];
t?u[o]=t[r]:u[o[0]]=o[1]}return u},f.select=k,f.tail=V,f.unique=G,f.chain=function(n){return n=new c(n),n.__chain__=Q,n},f.clone=function(n){return A(n)?Ut(n)?zt.call(n):y({},n):n},f.contains=S,f.escape=function(n){return n==X?"":(n+"").replace(ut,s)},f.every=N,f.find=B,f.has=function(n,t){return n?Et.call(n,t):Y},f.identity=K,f.indexOf=U,f.isArguments=h,f.isArray=Ut,f.isBoolean=function(n){return n===Q||n===Y||kt.call(n)==ft},f.isDate=function(n){return n?typeof n=="object"&&kt.call(n)==ct:Y},f.isElement=function(n){return n?1===n.nodeType:Y
},f.isEmpty=b,f.isEqual=j,f.isFinite=function(n){return Rt(n)&&!Dt(parseFloat(n))},f.isFunction=w,f.isNaN=function(n){return x(n)&&n!=+n},f.isNull=function(n){return n===X},f.isNumber=x,f.isObject=A,f.isRegExp=function(n){return!(!n||!gt[typeof n])&&kt.call(n)==st},f.isString=O,f.isUndefined=function(n){return typeof n=="undefined"},f.lastIndexOf=function(n,t,r){var e=n?n.length:0;for(typeof r=="number"&&(e=(0>r?Tt(0,e+r):$t(r,e-1))+1);e--;)if(n[e]===t)return e;return-1},f.mixin=L,f.noConflict=function(){return n._=bt,this
},f.random=function(n,t){n==X&&t==X&&(t=1),n=+n||0,t==X?(t=n,n=0):t=+t||0;var r=It();return n%1||t%1?n+$t(r*(t-n+parseFloat("1e-"+((r+"").length-1))),t):n+Ot(r*(t-n+1))},f.reduce=M,f.reduceRight=T,f.result=function(n,t){var r=n?n[t]:X;return w(r)?n[t]():r},f.size=function(n){var t=n?n.length:0;return typeof t=="number"?t:Vt(n).length},f.some=$,f.sortedIndex=W,f.template=function(n,t,r){var e=f.templateSettings;n||(n=""),r=m({},r,e);var u=0,o="__p+='",e=r.variable;n.replace(RegExp((r.escape||et).source+"|"+(r.interpolate||et).source+"|"+(r.evaluate||et).source+"|$","g"),function(t,r,e,a,f){return o+=n.slice(u,f).replace(ot,i),r&&(o+="'+_['escape']("+r+")+'"),a&&(o+="';"+a+";__p+='"),e&&(o+="'+((__t=("+e+"))==null?'':__t)+'"),u=f+t.length,t
}),o+="';\n",e||(e="obj",o="with("+e+"||{}){"+o+"}"),o="function("+e+"){var __t,__p='',__j=Array.prototype.join;function print(){__p+=__j.call(arguments,'')}"+o+"return __p}";try{var a=Function("_","return "+o)(f)}catch(c){throw c.source=o,c}return t?a(t):(a.source=o,a)},f.unescape=function(n){return n==X?"":(n+"").replace(rt,g)},f.uniqueId=function(n){var t=++Z+"";return n?n+t:t},f.all=N,f.any=$,f.detect=B,f.findWhere=function(n,t){return I(n,t,Q)},f.foldl=M,f.foldr=T,f.include=S,f.inject=M,f.first=C,f.last=function(n,t,r){if(n){var e=0,u=n.length;
if(typeof t!="number"&&t!=X){var o=u;for(t=J(t,r);o--&&t(n[o],o,n);)e++}else if(e=t,e==X||r)return n[u-1];return zt.call(n,Tt(0,u-e))}},f.take=C,f.head=C,f.VERSION="1.3.1",L(f),f.prototype.chain=function(){return this.__chain__=Q,this},f.prototype.value=function(){return this.__wrapped__},F("pop push reverse shift sort splice unshift".split(" "),function(n){var t=dt[n];f.prototype[n]=function(){var n=this.__wrapped__;return t.apply(n,arguments),!Pt.spliceObjects&&0===n.length&&delete n[0],this}}),F(["concat","join","slice"],function(n){var t=dt[n];
f.prototype[n]=function(){var n=t.apply(this.__wrapped__,arguments);return this.__chain__&&(n=new c(n),n.__chain__=Q),n}}),typeof define=="function"&&typeof define.amd=="object"&&define.amd?(n._=f, define('underscore',[],function(){return f})):yt&&!yt.nodeType?mt?(mt.exports=f)._=f:yt._=f:n._=f}(this);
(function(){var root=this;var previousBackbone=root.Backbone;var array=[];var push=array.push;var slice=array.slice;var splice=array.splice;var Backbone;if(typeof exports!=="undefined"){Backbone=exports}else{Backbone=root.Backbone={}}Backbone.VERSION="1.0.0";var _=root._;if(!_&&typeof require!=="undefined")_=require("underscore");Backbone.$=root.jQuery||root.Zepto||root.ender||root.$;Backbone.noConflict=function(){root.Backbone=previousBackbone;return this};Backbone.emulateHTTP=false;Backbone.emulateJSON=false;var Events=Backbone.Events={on:function(name,callback,context){if(!eventsApi(this,"on",name,[callback,context])||!callback)return this;this._events||(this._events={});var events=this._events[name]||(this._events[name]=[]);events.push({callback:callback,context:context,ctx:context||this});return this},once:function(name,callback,context){if(!eventsApi(this,"once",name,[callback,context])||!callback)return this;var self=this;var once=_.once(function(){self.off(name,once);callback.apply(this,arguments)});once._callback=callback;return this.on(name,once,context)},off:function(name,callback,context){var retain,ev,events,names,i,l,j,k;if(!this._events||!eventsApi(this,"off",name,[callback,context]))return this;if(!name&&!callback&&!context){this._events={};return this}names=name?[name]:_.keys(this._events);for(i=0,l=names.length;i<l;i++){name=names[i];if(events=this._events[name]){this._events[name]=retain=[];if(callback||context){for(j=0,k=events.length;j<k;j++){ev=events[j];if(callback&&callback!==ev.callback&&callback!==ev.callback._callback||context&&context!==ev.context){retain.push(ev)}}}if(!retain.length)delete this._events[name]}}return this},trigger:function(name){if(!this._events)return this;var args=slice.call(arguments,1);if(!eventsApi(this,"trigger",name,args))return this;var events=this._events[name];var allEvents=this._events.all;if(events)triggerEvents(events,args);if(allEvents)triggerEvents(allEvents,arguments);return this},stopListening:function(obj,name,callback){var listeners=this._listeners;if(!listeners)return this;var deleteListener=!name&&!callback;if(typeof name==="object")callback=this;if(obj)(listeners={})[obj._listenerId]=obj;for(var id in listeners){listeners[id].off(name,callback,this);if(deleteListener)delete this._listeners[id]}return this}};var eventSplitter=/\s+/;var eventsApi=function(obj,action,name,rest){if(!name)return true;if(typeof name==="object"){for(var key in name){obj[action].apply(obj,[key,name[key]].concat(rest))}return false}if(eventSplitter.test(name)){var names=name.split(eventSplitter);for(var i=0,l=names.length;i<l;i++){obj[action].apply(obj,[names[i]].concat(rest))}return false}return true};var triggerEvents=function(events,args){var ev,i=-1,l=events.length,a1=args[0],a2=args[1],a3=args[2];switch(args.length){case 0:while(++i<l)(ev=events[i]).callback.call(ev.ctx);return;case 1:while(++i<l)(ev=events[i]).callback.call(ev.ctx,a1);return;case 2:while(++i<l)(ev=events[i]).callback.call(ev.ctx,a1,a2);return;case 3:while(++i<l)(ev=events[i]).callback.call(ev.ctx,a1,a2,a3);return;default:while(++i<l)(ev=events[i]).callback.apply(ev.ctx,args)}};var listenMethods={listenTo:"on",listenToOnce:"once"};_.each(listenMethods,function(implementation,method){Events[method]=function(obj,name,callback){var listeners=this._listeners||(this._listeners={});var id=obj._listenerId||(obj._listenerId=_.uniqueId("l"));listeners[id]=obj;if(typeof name==="object")callback=this;obj[implementation](name,callback,this);return this}});Events.bind=Events.on;Events.unbind=Events.off;_.extend(Backbone,Events);var Model=Backbone.Model=function(attributes,options){var defaults;var attrs=attributes||{};options||(options={});this.cid=_.uniqueId("c");this.attributes={};_.extend(this,_.pick(options,modelOptions));if(options.parse)attrs=this.parse(attrs,options)||{};if(defaults=_.result(this,"defaults")){attrs=_.defaults({},attrs,defaults)}this.set(attrs,options);this.changed={};this.initialize.apply(this,arguments)};var modelOptions=["url","urlRoot","collection"];_.extend(Model.prototype,Events,{changed:null,validationError:null,idAttribute:"id",initialize:function(){},toJSON:function(options){return _.clone(this.attributes)},sync:function(){return Backbone.sync.apply(this,arguments)},get:function(attr){return this.attributes[attr]},escape:function(attr){return _.escape(this.get(attr))},has:function(attr){return this.get(attr)!=null},set:function(key,val,options){var attr,attrs,unset,changes,silent,changing,prev,current;if(key==null)return this;if(typeof key==="object"){attrs=key;options=val}else{(attrs={})[key]=val}options||(options={});if(!this._validate(attrs,options))return false;unset=options.unset;silent=options.silent;changes=[];changing=this._changing;this._changing=true;if(!changing){this._previousAttributes=_.clone(this.attributes);this.changed={}}current=this.attributes,prev=this._previousAttributes;if(this.idAttribute in attrs)this.id=attrs[this.idAttribute];for(attr in attrs){val=attrs[attr];if(!_.isEqual(current[attr],val))changes.push(attr);if(!_.isEqual(prev[attr],val)){this.changed[attr]=val}else{delete this.changed[attr]}unset?delete current[attr]:current[attr]=val}if(!silent){if(changes.length)this._pending=true;for(var i=0,l=changes.length;i<l;i++){this.trigger("change:"+changes[i],this,current[changes[i]],options)}}if(changing)return this;if(!silent){while(this._pending){this._pending=false;this.trigger("change",this,options)}}this._pending=false;this._changing=false;return this},unset:function(attr,options){return this.set(attr,void 0,_.extend({},options,{unset:true}))},clear:function(options){var attrs={};for(var key in this.attributes)attrs[key]=void 0;return this.set(attrs,_.extend({},options,{unset:true}))},hasChanged:function(attr){if(attr==null)return!_.isEmpty(this.changed);return _.has(this.changed,attr)},changedAttributes:function(diff){if(!diff)return this.hasChanged()?_.clone(this.changed):false;var val,changed=false;var old=this._changing?this._previousAttributes:this.attributes;for(var attr in diff){if(_.isEqual(old[attr],val=diff[attr]))continue;(changed||(changed={}))[attr]=val}return changed},previous:function(attr){if(attr==null||!this._previousAttributes)return null;return this._previousAttributes[attr]},previousAttributes:function(){return _.clone(this._previousAttributes)},fetch:function(options){options=options?_.clone(options):{};if(options.parse===void 0)options.parse=true;var model=this;var success=options.success;options.success=function(resp){if(!model.set(model.parse(resp,options),options))return false;if(success)success(model,resp,options);model.trigger("sync",model,resp,options)};wrapError(this,options);return this.sync("read",this,options)},save:function(key,val,options){var attrs,method,xhr,attributes=this.attributes;if(key==null||typeof key==="object"){attrs=key;options=val}else{(attrs={})[key]=val}if(attrs&&(!options||!options.wait)&&!this.set(attrs,options))return false;options=_.extend({validate:true},options);if(!this._validate(attrs,options))return false;if(attrs&&options.wait){this.attributes=_.extend({},attributes,attrs)}if(options.parse===void 0)options.parse=true;var model=this;var success=options.success;options.success=function(resp){model.attributes=attributes;var serverAttrs=model.parse(resp,options);if(options.wait)serverAttrs=_.extend(attrs||{},serverAttrs);if(_.isObject(serverAttrs)&&!model.set(serverAttrs,options)){return false}if(success)success(model,resp,options);model.trigger("sync",model,resp,options)};wrapError(this,options);method=this.isNew()?"create":options.patch?"patch":"update";if(method==="patch")options.attrs=attrs;xhr=this.sync(method,this,options);if(attrs&&options.wait)this.attributes=attributes;return xhr},destroy:function(options){options=options?_.clone(options):{};var model=this;var success=options.success;var destroy=function(){model.trigger("destroy",model,model.collection,options)};options.success=function(resp){if(options.wait||model.isNew())destroy();if(success)success(model,resp,options);if(!model.isNew())model.trigger("sync",model,resp,options)};if(this.isNew()){options.success();return false}wrapError(this,options);var xhr=this.sync("delete",this,options);if(!options.wait)destroy();return xhr},url:function(){var base=_.result(this,"urlRoot")||_.result(this.collection,"url")||urlError();if(this.isNew())return base;return base+(base.charAt(base.length-1)==="/"?"":"/")+encodeURIComponent(this.id)},parse:function(resp,options){return resp},clone:function(){return new this.constructor(this.attributes)},isNew:function(){return this.id==null},isValid:function(options){return this._validate({},_.extend(options||{},{validate:true}))},_validate:function(attrs,options){if(!options.validate||!this.validate)return true;attrs=_.extend({},this.attributes,attrs);var error=this.validationError=this.validate(attrs,options)||null;if(!error)return true;this.trigger("invalid",this,error,_.extend(options||{},{validationError:error}));return false}});var modelMethods=["keys","values","pairs","invert","pick","omit"];_.each(modelMethods,function(method){Model.prototype[method]=function(){var args=slice.call(arguments);args.unshift(this.attributes);return _[method].apply(_,args)}});var Collection=Backbone.Collection=function(models,options){options||(options={});if(options.url)this.url=options.url;if(options.model)this.model=options.model;if(options.comparator!==void 0)this.comparator=options.comparator;this._reset();this.initialize.apply(this,arguments);if(models)this.reset(models,_.extend({silent:true},options))};var setOptions={add:true,remove:true,merge:true};var addOptions={add:true,merge:false,remove:false};_.extend(Collection.prototype,Events,{model:Model,initialize:function(){},toJSON:function(options){return this.map(function(model){return model.toJSON(options)})},sync:function(){return Backbone.sync.apply(this,arguments)},add:function(models,options){return this.set(models,_.defaults(options||{},addOptions))},remove:function(models,options){models=_.isArray(models)?models.slice():[models];options||(options={});var i,l,index,model;for(i=0,l=models.length;i<l;i++){model=this.get(models[i]);if(!model)continue;delete this._byId[model.id];delete this._byId[model.cid];index=this.indexOf(model);this.models.splice(index,1);this.length--;if(!options.silent){options.index=index;model.trigger("remove",model,this,options)}this._removeReference(model)}return this},set:function(models,options){options=_.defaults(options||{},setOptions);if(options.parse)models=this.parse(models,options);if(!_.isArray(models))models=models?[models]:[];var i,l,model,attrs,existing,sort;var at=options.at;var sortable=this.comparator&&at==null&&options.sort!==false;var sortAttr=_.isString(this.comparator)?this.comparator:null;var toAdd=[],toRemove=[],modelMap={};for(i=0,l=models.length;i<l;i++){if(!(model=this._prepareModel(models[i],options)))continue;if(existing=this.get(model)){if(options.remove)modelMap[existing.cid]=true;if(options.merge){existing.set(model.attributes,options);if(sortable&&!sort&&existing.hasChanged(sortAttr))sort=true}}else if(options.add){toAdd.push(model);model.on("all",this._onModelEvent,this);this._byId[model.cid]=model;if(model.id!=null)this._byId[model.id]=model}}if(options.remove){for(i=0,l=this.length;i<l;++i){if(!modelMap[(model=this.models[i]).cid])toRemove.push(model)}if(toRemove.length)this.remove(toRemove,options)}if(toAdd.length){if(sortable)sort=true;this.length+=toAdd.length;if(at!=null){splice.apply(this.models,[at,0].concat(toAdd))}else{push.apply(this.models,toAdd)}}if(sort)this.sort({silent:true});if(options.silent)return this;for(i=0,l=toAdd.length;i<l;i++){(model=toAdd[i]).trigger("add",model,this,options)}if(sort)this.trigger("sort",this,options);return this},reset:function(models,options){options||(options={});for(var i=0,l=this.models.length;i<l;i++){this._removeReference(this.models[i])}options.previousModels=this.models;this._reset();this.add(models,_.extend({silent:true},options));if(!options.silent)this.trigger("reset",this,options);return this},push:function(model,options){model=this._prepareModel(model,options);this.add(model,_.extend({at:this.length},options));return model},pop:function(options){var model=this.at(this.length-1);this.remove(model,options);return model},unshift:function(model,options){model=this._prepareModel(model,options);this.add(model,_.extend({at:0},options));return model},shift:function(options){var model=this.at(0);this.remove(model,options);return model},slice:function(begin,end){return this.models.slice(begin,end)},get:function(obj){if(obj==null)return void 0;return this._byId[obj.id!=null?obj.id:obj.cid||obj]},at:function(index){return this.models[index]},where:function(attrs,first){if(_.isEmpty(attrs))return first?void 0:[];return this[first?"find":"filter"](function(model){for(var key in attrs){if(attrs[key]!==model.get(key))return false}return true})},findWhere:function(attrs){return this.where(attrs,true)},sort:function(options){if(!this.comparator)throw new Error("Cannot sort a set without a comparator");options||(options={});if(_.isString(this.comparator)||this.comparator.length===1){this.models=this.sortBy(this.comparator,this)}else{this.models.sort(_.bind(this.comparator,this))}if(!options.silent)this.trigger("sort",this,options);return this},sortedIndex:function(model,value,context){value||(value=this.comparator);var iterator=_.isFunction(value)?value:function(model){return model.get(value)};return _.sortedIndex(this.models,model,iterator,context)},pluck:function(attr){return _.invoke(this.models,"get",attr)},fetch:function(options){options=options?_.clone(options):{};if(options.parse===void 0)options.parse=true;var success=options.success;var collection=this;options.success=function(resp){var method=options.reset?"reset":"set";collection[method](resp,options);if(success)success(collection,resp,options);collection.trigger("sync",collection,resp,options)};wrapError(this,options);return this.sync("read",this,options)},create:function(model,options){options=options?_.clone(options):{};if(!(model=this._prepareModel(model,options)))return false;if(!options.wait)this.add(model,options);var collection=this;var success=options.success;options.success=function(resp){if(options.wait)collection.add(model,options);if(success)success(model,resp,options)};model.save(null,options);return model},parse:function(resp,options){return resp},clone:function(){return new this.constructor(this.models)},_reset:function(){this.length=0;this.models=[];this._byId={}},_prepareModel:function(attrs,options){if(attrs instanceof Model){if(!attrs.collection)attrs.collection=this;return attrs}options||(options={});options.collection=this;var model=new this.model(attrs,options);if(!model._validate(attrs,options)){this.trigger("invalid",this,attrs,options);return false}return model},_removeReference:function(model){if(this===model.collection)delete model.collection;model.off("all",this._onModelEvent,this)},_onModelEvent:function(event,model,collection,options){if((event==="add"||event==="remove")&&collection!==this)return;if(event==="destroy")this.remove(model,options);if(model&&event==="change:"+model.idAttribute){delete this._byId[model.previous(model.idAttribute)];if(model.id!=null)this._byId[model.id]=model}this.trigger.apply(this,arguments)}});var methods=["forEach","each","map","collect","reduce","foldl","inject","reduceRight","foldr","find","detect","filter","select","reject","every","all","some","any","include","contains","invoke","max","min","toArray","size","first","head","take","initial","rest","tail","drop","last","without","indexOf","shuffle","lastIndexOf","isEmpty","chain"];_.each(methods,function(method){Collection.prototype[method]=function(){var args=slice.call(arguments);args.unshift(this.models);return _[method].apply(_,args)}});var attributeMethods=["groupBy","countBy","sortBy"];_.each(attributeMethods,function(method){Collection.prototype[method]=function(value,context){var iterator=_.isFunction(value)?value:function(model){return model.get(value)};return _[method](this.models,iterator,context)}});var View=Backbone.View=function(options){this.cid=_.uniqueId("view");this._configure(options||{});this._ensureElement();this.initialize.apply(this,arguments);this.delegateEvents()};var delegateEventSplitter=/^(\S+)\s*(.*)$/;var viewOptions=["model","collection","el","id","attributes","className","tagName","events"];_.extend(View.prototype,Events,{tagName:"div",$:function(selector){return this.$el.find(selector)},initialize:function(){},render:function(){return this},remove:function(){this.$el.remove();this.stopListening();return this},setElement:function(element,delegate){if(this.$el)this.undelegateEvents();this.$el=element instanceof Backbone.$?element:Backbone.$(element);this.el=this.$el[0];if(delegate!==false)this.delegateEvents();return this},delegateEvents:function(events){if(!(events||(events=_.result(this,"events"))))return this;this.undelegateEvents();for(var key in events){var method=events[key];if(!_.isFunction(method))method=this[events[key]];if(!method)continue;var match=key.match(delegateEventSplitter);var eventName=match[1],selector=match[2];method=_.bind(method,this);eventName+=".delegateEvents"+this.cid;if(selector===""){this.$el.on(eventName,method)}else{this.$el.on(eventName,selector,method)}}return this},undelegateEvents:function(){this.$el.off(".delegateEvents"+this.cid);return this},_configure:function(options){if(this.options)options=_.extend({},_.result(this,"options"),options);_.extend(this,_.pick(options,viewOptions));this.options=options},_ensureElement:function(){if(!this.el){var attrs=_.extend({},_.result(this,"attributes"));if(this.id)attrs.id=_.result(this,"id");if(this.className)attrs["class"]=_.result(this,"className");var $el=Backbone.$("<"+_.result(this,"tagName")+">").attr(attrs);this.setElement($el,false)}else{this.setElement(_.result(this,"el"),false)}}});Backbone.sync=function(method,model,options){var type=methodMap[method];_.defaults(options||(options={}),{emulateHTTP:Backbone.emulateHTTP,emulateJSON:Backbone.emulateJSON});var params={type:type,dataType:"json"};if(!options.url){params.url=_.result(model,"url")||urlError()}if(options.data==null&&model&&(method==="create"||method==="update"||method==="patch")){params.contentType="application/json";params.data=JSON.stringify(options.attrs||model.toJSON(options))}if(options.emulateJSON){params.contentType="application/x-www-form-urlencoded";params.data=params.data?{model:params.data}:{}}if(options.emulateHTTP&&(type==="PUT"||type==="DELETE"||type==="PATCH")){params.type="POST";if(options.emulateJSON)params.data._method=type;var beforeSend=options.beforeSend;options.beforeSend=function(xhr){xhr.setRequestHeader("X-HTTP-Method-Override",type);if(beforeSend)return beforeSend.apply(this,arguments)}}if(params.type!=="GET"&&!options.emulateJSON){params.processData=false}if(params.type==="PATCH"&&window.ActiveXObject&&!(window.external&&window.external.msActiveXFilteringEnabled)){params.xhr=function(){return new ActiveXObject("Microsoft.XMLHTTP")}}var xhr=options.xhr=Backbone.ajax(_.extend(params,options));model.trigger("request",model,xhr,options);return xhr};var methodMap={create:"POST",update:"PUT",patch:"PATCH","delete":"DELETE",read:"GET"};Backbone.ajax=function(){return Backbone.$.ajax.apply(Backbone.$,arguments)};var Router=Backbone.Router=function(options){options||(options={});if(options.routes)this.routes=options.routes;this._bindRoutes();this.initialize.apply(this,arguments)};var optionalParam=/\((.*?)\)/g;var namedParam=/(\(\?)?:\w+/g;var splatParam=/\*\w+/g;var escapeRegExp=/[\-{}\[\]+?.,\\\^$|#\s]/g;_.extend(Router.prototype,Events,{initialize:function(){},route:function(route,name,callback){if(!_.isRegExp(route))route=this._routeToRegExp(route);if(_.isFunction(name)){callback=name;name=""}if(!callback)callback=this[name];var router=this;Backbone.history.route(route,function(fragment){var args=router._extractParameters(route,fragment);callback&&callback.apply(router,args);router.trigger.apply(router,["route:"+name].concat(args));router.trigger("route",name,args);Backbone.history.trigger("route",router,name,args)});return this},navigate:function(fragment,options){Backbone.history.navigate(fragment,options);return this},_bindRoutes:function(){if(!this.routes)return;this.routes=_.result(this,"routes");var route,routes=_.keys(this.routes);while((route=routes.pop())!=null){this.route(route,this.routes[route])}},_routeToRegExp:function(route){route=route.replace(escapeRegExp,"\\$&").replace(optionalParam,"(?:$1)?").replace(namedParam,function(match,optional){return optional?match:"([^/]+)"}).replace(splatParam,"(.*?)");return new RegExp("^"+route+"$")},_extractParameters:function(route,fragment){var params=route.exec(fragment).slice(1);return _.map(params,function(param){return param?decodeURIComponent(param):null})}});var History=Backbone.History=function(){this.handlers=[];_.bindAll(this,"checkUrl");if(typeof window!=="undefined"){this.location=window.location;this.history=window.history}};var routeStripper=/^[#\/]|\s+$/g;var rootStripper=/^\/+|\/+$/g;var isExplorer=/msie [\w.]+/;var trailingSlash=/\/$/;History.started=false;_.extend(History.prototype,Events,{interval:50,getHash:function(window){var match=(window||this).location.href.match(/#(.*)$/);return match?match[1]:""},getFragment:function(fragment,forcePushState){if(fragment==null){if(this._hasPushState||!this._wantsHashChange||forcePushState){fragment=this.location.pathname;var root=this.root.replace(trailingSlash,"");if(!fragment.indexOf(root))fragment=fragment.substr(root.length)}else{fragment=this.getHash()}}return fragment.replace(routeStripper,"")},start:function(options){if(History.started)throw new Error("Backbone.history has already been started");History.started=true;this.options=_.extend({},{root:"/"},this.options,options);this.root=this.options.root;this._wantsHashChange=this.options.hashChange!==false;this._wantsPushState=!!this.options.pushState;this._hasPushState=!!(this.options.pushState&&this.history&&this.history.pushState);var fragment=this.getFragment();var docMode=document.documentMode;var oldIE=isExplorer.exec(navigator.userAgent.toLowerCase())&&(!docMode||docMode<=7);this.root=("/"+this.root+"/").replace(rootStripper,"/");if(oldIE&&this._wantsHashChange){this.iframe=Backbone.$('<iframe src="javascript:0" tabindex="-1" />').hide().appendTo("body")[0].contentWindow;this.navigate(fragment)}if(this._hasPushState){Backbone.$(window).on("popstate",this.checkUrl)}else if(this._wantsHashChange&&"onhashchange"in window&&!oldIE){Backbone.$(window).on("hashchange",this.checkUrl)}else if(this._wantsHashChange){this._checkUrlInterval=setInterval(this.checkUrl,this.interval)}this.fragment=fragment;var loc=this.location;var atRoot=loc.pathname.replace(/[^\/]$/,"$&/")===this.root;if(this._wantsHashChange&&this._wantsPushState&&!this._hasPushState&&!atRoot){this.fragment=this.getFragment(null,true);this.location.replace(this.root+this.location.search+"#"+this.fragment);return true}else if(this._wantsPushState&&this._hasPushState&&atRoot&&loc.hash){this.fragment=this.getHash().replace(routeStripper,"");this.history.replaceState({},document.title,this.root+this.fragment+loc.search)}if(!this.options.silent)return this.loadUrl()},stop:function(){Backbone.$(window).off("popstate",this.checkUrl).off("hashchange",this.checkUrl);clearInterval(this._checkUrlInterval);History.started=false},route:function(route,callback){this.handlers.unshift({route:route,callback:callback})},checkUrl:function(e){var current=this.getFragment();if(current===this.fragment&&this.iframe){current=this.getFragment(this.getHash(this.iframe))}if(current===this.fragment)return false;if(this.iframe)this.navigate(current);this.loadUrl()||this.loadUrl(this.getHash())},loadUrl:function(fragmentOverride){var fragment=this.fragment=this.getFragment(fragmentOverride);var matched=_.any(this.handlers,function(handler){if(handler.route.test(fragment)){handler.callback(fragment);return true}});return matched},navigate:function(fragment,options){if(!History.started)return false;if(!options||options===true)options={trigger:options};fragment=this.getFragment(fragment||"");if(this.fragment===fragment)return;this.fragment=fragment;var url=this.root+fragment;if(this._hasPushState){this.history[options.replace?"replaceState":"pushState"]({},document.title,url)}else if(this._wantsHashChange){this._updateHash(this.location,fragment,options.replace);if(this.iframe&&fragment!==this.getFragment(this.getHash(this.iframe))){if(!options.replace)this.iframe.document.open().close();this._updateHash(this.iframe.location,fragment,options.replace)}}else{return this.location.assign(url)}if(options.trigger)this.loadUrl(fragment)},_updateHash:function(location,fragment,replace){if(replace){var href=location.href.replace(/(javascript:|#).*$/,"");location.replace(href+"#"+fragment)}else{location.hash="#"+fragment}}});Backbone.history=new History;var extend=function(protoProps,staticProps){var parent=this;var child;if(protoProps&&_.has(protoProps,"constructor")){child=protoProps.constructor}else{child=function(){return parent.apply(this,arguments)}}_.extend(child,parent,staticProps);var Surrogate=function(){this.constructor=child};Surrogate.prototype=parent.prototype;child.prototype=new Surrogate;if(protoProps)_.extend(child.prototype,protoProps);child.__super__=parent.prototype;return child};Model.extend=Collection.extend=Router.extend=View.extend=History.extend=extend;var urlError=function(){throw new Error('A "url" property or function must be specified')};var wrapError=function(model,options){var error=options.error;options.error=function(resp){if(error)error(model,resp,options);model.trigger("error",model,resp,options)}}}).call(this);
/*
//@ sourceMappingURL=backbone-min.map
*/;
define("backbone", ["jquery","underscore"], (function (global) {
    return function () {
        var ret, fn;
        return ret || global.Backbone;
    };
}(this)));

(function($) {

  // Backbone.Stickit Namespace
  // --------------------------

  Backbone.Stickit = {

    _handlers: [],

    addHandler: function(handlers) {
      // Fill-in default values.
      handlers = _.map(_.flatten([handlers]), function(handler) {
        return _.extend({
          updateModel: true,
          updateView: true,
          updateMethod: 'text'
        }, handler);
      });
      this._handlers = this._handlers.concat(handlers);
    }
  };

  // Backbone.View Mixins
  // --------------------

  _.extend(Backbone.View.prototype, {

    // Collection of model event bindings.
    //   [{model,event,fn}, ...]
    _modelBindings: null,

    // Unbind the model and event bindings from `this._modelBindings` and
    // `this.$el`. If the optional `model` parameter is defined, then only
    // delete bindings for the given `model` and its corresponding view events.
    unstickit: function(model) {
      _.each(this._modelBindings, _.bind(function(binding, i) {
        if (model && binding.model !== model) return false;
        binding.model.off(binding.event, binding.fn);
        delete this._modelBindings[i];
      }, this));
      this._modelBindings = _.compact(this._modelBindings);

      this.$el.off('.stickit' + (model ? '.' + model.cid : ''));
    },

    // Using `this.bindings` configuration or the `optionalBindingsConfig`, binds `this.model`
    // or the `optionalModel` to elements in the view.
    stickit: function(optionalModel, optionalBindingsConfig) {
      var self = this,
        model = optionalModel || this.model,
        namespace = '.stickit.' + model.cid,
        bindings = optionalBindingsConfig || this.bindings || {};

      this._modelBindings || (this._modelBindings = []);
      this.unstickit(model);

      // Iterate through the selectors in the bindings configuration and configure
      // the various options for each field.
      _.each(_.keys(bindings), function(selector) {
        var $el, options, modelAttr, config,
          binding = bindings[selector] || {},
          bindKey = _.uniqueId();

        // Support ':el' selector - special case selector for the view managed delegate.
        if (selector != ':el') $el = self.$(selector);
        else {
          $el = self.$el;
          selector = '';
        }

        // Fail fast if the selector didn't match an element.
        if (!$el.length) return;

        // Allow shorthand setting of model attributes - `'selector':'observe'`.
        if (_.isString(binding)) binding = {observe:binding};

        config = getConfiguration($el, binding);

        modelAttr = config.observe;

        // Create the model set options with a unique `bindKey` so that we
        // can avoid double-binding in the `change:attribute` event handler.
        options = _.extend({bindKey:bindKey}, config.setOptions || {});

        initializeAttributes(self, $el, config, model, modelAttr);

        initializeVisible(self, $el, config, model, modelAttr);

        if (modelAttr) {
          // Setup one-way, form element to model, bindings.
          _.each(config.events || [], function(type) {
            var event = type + namespace;
            var method = function(event) {
              var val = config.getVal.call(self, $el, event, config);
              // Don't update the model if false is returned from the `updateModel` configuration.
              if (evaluateBoolean(self, config.updateModel, val, config))
                setAttr(model, modelAttr, val, options, self, config);
            };
            if (selector === '') self.$el.on(event, method);
            else self.$el.on(event, selector, method);
          });

          // Setup a `change:modelAttr` observer to keep the view element in sync.
          // `modelAttr` may be an array of attributes or a single string value.
          _.each(_.flatten([modelAttr]), function(attr) {
            observeModelEvent(model, self, 'change:'+attr, function(model, val, options) {
              if (options == null || options.bindKey != bindKey)
                updateViewBindEl(self, $el, config, getAttr(model, modelAttr, config, self), model);
            });
          });

          updateViewBindEl(self, $el, config, getAttr(model, modelAttr, config, self), model, true);
        }

        // After each binding is setup, call the `initialize` callback.
        applyViewFn(self, config.initialize, $el, model, config);
      });

      // Wrap `view.remove` to unbind stickit model and dom events.
      this.remove = _.wrap(this.remove, function(oldRemove) {
        self.unstickit();
        if (oldRemove) oldRemove.call(self);
      });
    }
  });

  // Helpers
  // -------

  // Evaluates the given `path` (in object/dot-notation) relative to the given
  // `obj`. If the path is null/undefined, then the given `obj` is returned.
  var evaluatePath = function(obj, path) {
    var parts = (path || '').split('.');
    var result = _.reduce(parts, function(memo, i) { return memo[i]; }, obj);
    return result == null ? obj : result;
  };

  // If the given `fn` is a string, then view[fn] is called, otherwise it is
  // a function that should be executed.
  var applyViewFn = function(view, fn) {
    if (fn) return (_.isString(fn) ? view[fn] : fn).apply(view, _.toArray(arguments).slice(2));
  };

  var getSelectedOption = function($select) { return $select.find('option').not(function(){ return !this.selected; }); };

  // Given a function, string (view function reference), or a boolean
  // value, returns the truthy result. Any other types evaluate as false.
  var evaluateBoolean = function(view, reference) {
    if (_.isBoolean(reference)) return reference;
    else if (_.isFunction(reference) || _.isString(reference))
      return applyViewFn.apply(this, _.toArray(arguments));
    return false;
  };

  // Setup a model event binding with the given function, and track the event
  // in the view's _modelBindings.
  var observeModelEvent = function(model, view, event, fn) {
    model.on(event, fn, view);
    view._modelBindings.push({model:model, event:event, fn:fn});
  };

  // Prepares the given `val`ue and sets it into the `model`.
  var setAttr = function(model, attr, val, options, context, config) {
    if (config.onSet) val = applyViewFn(context, config.onSet, val, config);
    model.set(attr, val, options);
  };

  // Returns the given `attr`'s value from the `model`, escaping and
  // formatting if necessary. If `attr` is an array, then an array of
  // respective values will be returned.
  var getAttr = function(model, attr, config, context) {
    var val, retrieveVal = function(field) {
      var retrieved = config.escape ? model.escape(field) : model.get(field);
      return _.isUndefined(retrieved) ? '' : retrieved;
    };
    val = _.isArray(attr) ? _.map(attr, retrieveVal) : retrieveVal(attr);
    return config.onGet ? applyViewFn(context, config.onGet, val, config) : val;
  };

  // Find handlers in `Backbone.Stickit._handlers` with selectors that match
  // `$el` and generate a configuration by mixing them in the order that they
  // were found with the with the givne `binding`.
  var getConfiguration = function($el, binding) {
    var handlers = [{
      updateModel: false,
      updateView: true,
      updateMethod: 'text',
      update: function($el, val, m, opts) { $el[opts.updateMethod](val); },
      getVal: function($el, e, opts) { return $el[opts.updateMethod](); }
    }];
    _.each(Backbone.Stickit._handlers, function(handler) {
      if ($el.is(handler.selector)) handlers.push(handler);
    });
    handlers.push(binding);
    var config = _.extend.apply(_, handlers);
    delete config.selector;
    return config;
  };

  // Setup the attributes configuration - a list that maps an attribute or
  // property `name`, to an `observe`d model attribute, using an optional
  // `onGet` formatter.
  //
  //     attributes: [{
  //       name: 'attributeOrPropertyName',
  //       observe: 'modelAttrName'
  //       onGet: function(modelAttrVal, modelAttrName) { ... }
  //     }, ...]
  //
  var initializeAttributes = function(view, $el, config, model, modelAttr) {
    var props = ['autofocus', 'autoplay', 'async', 'checked', 'controls', 'defer', 'disabled', 'hidden', 'loop', 'multiple', 'open', 'readonly', 'required', 'scoped', 'selected'];

    _.each(config.attributes || [], function(attrConfig) {
      var lastClass = '',
        observed = attrConfig.observe || (attrConfig.observe = modelAttr),
        updateAttr = function() {
          var updateType = _.indexOf(props, attrConfig.name, true) > -1 ? 'prop' : 'attr',
            val = getAttr(model, observed, attrConfig, view);
          // If it is a class then we need to remove the last value and add the new.
          if (attrConfig.name == 'class') {
            $el.removeClass(lastClass).addClass(val);
            lastClass = val;
          }
          else $el[updateType](attrConfig.name, val);
        };
      _.each(_.flatten([observed]), function(attr) {
        observeModelEvent(model, view, 'change:' + attr, updateAttr);
      });
      updateAttr();
    });
  };

  // If `visible` is configured, then the view element will be shown/hidden
  // based on the truthiness of the modelattr's value or the result of the
  // given callback. If a `visibleFn` is also supplied, then that callback
  // will be executed to manually handle showing/hiding the view element.
  //
  //     observe: 'isRight',
  //     visible: true, // or function(val, options) {}
  //     visibleFn: function($el, isVisible, options) {} // optional handler
  //
  var initializeVisible = function(view, $el, config, model, modelAttr) {
    if (config.visible == null) return;
    var visibleCb = function() {
      var visible = config.visible,
          visibleFn = config.visibleFn,
          val = getAttr(model, modelAttr, config, view),
          isVisible = !!val;
      // If `visible` is a function then it should return a boolean result to show/hide.
      if (_.isFunction(visible) || _.isString(visible)) isVisible = applyViewFn(view, visible, val, config);
      // Either use the custom `visibleFn`, if provided, or execute the standard show/hide.
      if (visibleFn) applyViewFn(view, visibleFn, $el, isVisible, config);
      else {
        if (isVisible) $el.show();
        else $el.hide();
      }
    };
    _.each(_.flatten([modelAttr]), function(attr) {
      observeModelEvent(model, view, 'change:' + attr, visibleCb);
    });
    visibleCb();
  };

  // Update the value of `$el` using the given configuration and trigger the
  // `afterUpdate` callback. This action may be blocked by `config.updateView`.
  //
  //     update: function($el, val, model, options) {},  // handler for updating
  //     updateView: true, // defaults to true
  //     afterUpdate: function($el, val, options) {} // optional callback
  //
  var updateViewBindEl = function(view, $el, config, val, model, isInitializing) {
    if (!evaluateBoolean(view, config.updateView, val, config)) return;
    config.update.call(view, $el, val, model, config);
    if (!isInitializing) applyViewFn(view, config.afterUpdate, $el, val, config);
  };

  // Default Handlers
  // ----------------

  Backbone.Stickit.addHandler([{
    selector: '[contenteditable="true"]',
    updateMethod: 'html',
    events: ['keyup', 'change', 'paste', 'cut']
  }, {
    selector: 'input',
    events: ['keyup', 'change', 'paste', 'cut'],
    update: function($el, val) { $el.val(val); },
    getVal: function($el) {
      var val = $el.val();
      if ($el.is('[type="number"]')) return val == null ? val : Number(val);
      else return val;
    }
  }, {
    selector: 'textarea',
    events: ['keyup', 'change', 'paste', 'cut'],
    update: function($el, val) { $el.val(val); },
    getVal: function($el) { return $el.val(); }
  }, {
    selector: 'input[type="radio"]',
    events: ['change'],
    update: function($el, val) {
      $el.filter('[value="'+val+'"]').prop('checked', true);
    },
    getVal: function($el) {
      return $el.filter(':checked').val();
    }
  }, {
    selector: 'input[type="checkbox"]',
    events: ['change'],
    update: function($el, val, model, options) {
      if ($el.length > 1) {
        // There are multiple checkboxes so we need to go through them and check
        // any that have value attributes that match what's in the array of `val`s.
        val || (val = []);
        _.each($el, function(el) {
          if (_.indexOf(val, $(el).val()) > -1) $(el).prop('checked', true);
          else $(el).prop('checked', false);
        });
      } else {
        if (_.isBoolean(val)) $el.prop('checked', val);
        else $el.prop('checked', val == $el.val());
      }
    },
    getVal: function($el) {
      var val;
      if ($el.length > 1) {
        val = _.reduce($el, function(memo, el) {
          if ($(el).prop('checked')) memo.push($(el).val());
          return memo;
        }, []);
      } else {
        val = $el.prop('checked');
        // If the checkbox has a value attribute defined, then
        // use that value. Most browsers use "on" as a default.
        var boxval = $el.val();
        if (boxval != 'on' && boxval != null) {
          if (val) val = $el.val();
          else val = null;
        }
      }
      return val;
    }
  }, {
    selector: 'select',
    events: ['change'],
    update: function($el, val, model, options) {
      var optList,
        selectConfig = options.selectOptions,
        list = selectConfig && selectConfig.collection || undefined,
        isMultiple = $el.prop('multiple');

      // If there are no `selectOptions` then we assume that the `<select>`
      // is pre-rendered and that we need to generate the collection.
      if (!selectConfig) {
        selectConfig = {};
        var getList = function($el) {
          return $el.find('option').map(function() {
            return {value:this.value, label:this.text};
          }).get();
        };
        if ($el.find('optgroup').length) {
          list = {opt_labels:[]};
          _.each($el.find('optgroup'), function(el) {
            var label = $(el).attr('label');
            list.opt_labels.push(label);
            list[label] = getList($(el));
          });
        } else {
          list = getList($el);
        }
      }

      // Fill in default label and path values.
      selectConfig.valuePath = selectConfig.valuePath || 'value';
      selectConfig.labelPath = selectConfig.labelPath || 'label';

      var addSelectOptions = function(optList, $el, fieldVal) {
        // Add a flag for default option at the beginning of the list.
        if (selectConfig.defaultOption) {
          optList = _.clone(optList);
          optList.unshift('__default__');
        }
        _.each(optList, function(obj) {
          var option = $('<option/>'), optionVal = obj;

          var fillOption = function(text, val) {
            option.text(text);
            optionVal = val;
            // Save the option value as data so that we can reference it later.
            option.data('stickit_bind_val', optionVal);
            if (!_.isArray(optionVal) && !_.isObject(optionVal)) option.val(optionVal);
          };

          if (obj === '__default__')
            fillOption(selectConfig.defaultOption.label, selectConfig.defaultOption.value);
          else
            fillOption(evaluatePath(obj, selectConfig.labelPath), evaluatePath(obj, selectConfig.valuePath));

          // Determine if this option is selected.
          if (!isMultiple && optionVal != null && fieldVal != null && optionVal == fieldVal || (_.isObject(fieldVal) && _.isEqual(optionVal, fieldVal)))
            option.prop('selected', true);
          else if (isMultiple && _.isArray(fieldVal)) {
            _.each(fieldVal, function(val) {
              if (_.isObject(val)) val = evaluatePath(val, selectConfig.valuePath);
              if (val == optionVal || (_.isObject(val) && _.isEqual(optionVal, val)))
                option.prop('selected', true);
            });
          }

          $el.append(option);
        });
      };

      $el.html('');

      // The `list` configuration is a function that returns the options list or a string
      // which represents the path to the list relative to `window` or the view/`this`.
      var evaluate = function(view, list) {
        var context = window;
        if (list.indexOf('this.') === 0) context = view;
        list = list.replace(/^[a-z]*\.(.+)$/, '$1');
        return evaluatePath(context, list);
      };
      if (_.isString(list)) optList = evaluate(this, list);
      else if (_.isFunction(list)) optList = applyViewFn(this, list, $el, options);
      else optList = list;

      // Support Backbone.Collection and deserialize.
      if (optList instanceof Backbone.Collection) optList = optList.toJSON();

      if (_.isArray(optList)) {
        addSelectOptions(optList, $el, val);
      } else {
        // If the optList is an object, then it should be used to define an optgroup. An
        // optgroup object configuration looks like the following:
        //
        //     {
        //       'opt_labels': ['Looney Tunes', 'Three Stooges'],
        //       'Looney Tunes': [{id: 1, name: 'Bugs Bunny'}, {id: 2, name: 'Donald Duck'}],
        //       'Three Stooges': [{id: 3, name : 'moe'}, {id: 4, name : 'larry'}, {id: 5, name : 'curly'}]
        //     }
        //
        _.each(optList.opt_labels, function(label) {
          var $group = $('<optgroup/>').attr('label', label);
          addSelectOptions(optList[label], $group, val);
          $el.append($group);
        });
      }
    },
    getVal: function($el) {
      var val;
      if ($el.prop('multiple')) {
        val = $(getSelectedOption($el).map(function() {
          return $(this).data('stickit_bind_val');
        })).get();
      } else {
        val = getSelectedOption($el).data('stickit_bind_val');
      }
      return val;
    }
  }]);

})(window.jQuery || window.Zepto);

define("stickit", ["backbone"], (function (global) {
    return function () {
        var ret, fn;
        return ret || global.Backbone.Stickit;
    };
}(this)));

// dropbox-datastores-0.1.0-b3.js
!function(){var t,e,r,n,i,o,s,a,u,l,h,c,p,d,f,_,y,g,m,v,w,b,S,D,A,O,E,x,U,C,P,T,k,R,I,L,j,N,F,B,M,X,z,H,q,W,V,J,K,G,$,Z,Q,Y,te,ee,re,ne,ie,oe,se,ae,ue,le,he,ce,pe,de,fe,_e,ye,ge,me,ve,we,be,Se,De,Ae,Oe,Ee,xe,Ue,Ce,Pe,Te,ke,Re,Ie,Le,je,Ne,Fe,Be,Me,Xe,ze,He,qe,We,Ve,Je,Ke,Ge,$e,Ze,Qe,Ye,tr,er,rr,nr,ir,or,sr=[].indexOf||function(t){for(var e=0,r=this.length;r>e;e++)if(e in this&&this[e]===t)return e;return-1},ar={}.hasOwnProperty,ur=function(t,e){function r(){this.constructor=t}for(var n in e)ar.call(e,n)&&(t[n]=e[n]);return r.prototype=e.prototype,t.prototype=new r,t.__super__=e.prototype,t},lr=[].slice;p=function(){return null},p.Util={},p.Http={},p.File={},p.Util.EventSource=function(){function t(t){this._cancelable=t&&t.cancelable,this._listeners=[]}return t.prototype.addListener=function(t){if("function"!=typeof t)throw new TypeError("Invalid listener type; expected function");return sr.call(this._listeners,t)<0&&this._listeners.push(t),this},t.prototype.removeListener=function(t){var e,r,n,i,o,s;if(this._listeners.indexOf)r=this._listeners.indexOf(t),-1!==r&&this._listeners.splice(r,1);else for(s=this._listeners,e=i=0,o=s.length;o>i;e=++i)if(n=s[e],n===t){this._listeners.splice(e,1);break}return this},t.prototype.dispatch=function(t){var e,r,n,i,o;for(o=this._listeners,n=0,i=o.length;i>n;n++)if(e=o[n],r=e(t),this._cancelable&&r===!1)return!1;return!0},t}(),p.Util.TypedEventSource=function(){function t(t){this.options=t,this._sources={}}return t.prototype._getSource=function(t){return this._sources[t]||(this._sources[t]=new p.Util.EventSource(this.options))},t.prototype.addListener=function(t,e){return this._getSource(t).addListener(e),this},t.prototype.removeListener=function(t,e){return this._getSource(t).removeListener(e),this},t.prototype.dispatch=function(t,e){return this._getSource(t).dispatch(e)},t}(),p.AccountInfo=function(){function t(t){var e;this._json=t,this.name=t.display_name,this.email=t.email,this.countryCode=t.country||null,this.uid=t.uid.toString(),t.public_app_url?(this.publicAppUrl=t.public_app_url,e=this.publicAppUrl.length-1,e>=0&&"/"===this.publicAppUrl.substring(e)&&(this.publicAppUrl=this.publicAppUrl.substring(0,e))):this.publicAppUrl=null,this.referralUrl=t.referral_link,this.quota=t.quota_info.quota,this.privateBytes=t.quota_info.normal||0,this.sharedBytes=t.quota_info.shared||0,this.usedQuota=this.privateBytes+this.sharedBytes}return t.parse=function(t){return t&&"object"==typeof t?new p.AccountInfo(t):t},t.prototype.name=null,t.prototype.email=null,t.prototype.countryCode=null,t.prototype.uid=null,t.prototype.referralUrl=null,t.prototype.publicAppUrl=null,t.prototype.quota=null,t.prototype.usedQuota=null,t.prototype.privateBytes=null,t.prototype.sharedBytes=null,t.prototype.json=function(){return this._json},t}(),p.ApiError=function(){function t(t,e,r){var n,i;if(this.method=e,this.url=r,this.status=t.status,t.responseType)try{n=t.response||t.responseText}catch(o){i=o;try{n=t.responseText}catch(o){i=o,n=null}}else try{n=t.responseText}catch(o){i=o,n=null}if(n)try{this.responseText=n.toString(),this.response=JSON.parse(n)}catch(o){i=o,this.response=null}else this.responseText="(no response)",this.response=null}return t.prototype.status=null,t.prototype.method=null,t.prototype.url=null,t.prototype.responseText=null,t.prototype.response=null,t.NETWORK_ERROR=0,t.NO_CONTENT=304,t.INVALID_PARAM=400,t.INVALID_TOKEN=401,t.OAUTH_ERROR=403,t.NOT_FOUND=404,t.INVALID_METHOD=405,t.NOT_ACCEPTABLE=406,t.CONFLICT=409,t.RATE_LIMITED=503,t.OVER_QUOTA=507,t.prototype.toString=function(){return"Dropbox API error "+this.status+" from "+this.method+" "+this.url+" :: "+this.responseText},t.prototype.inspect=function(){return this.toString()},t}(),p.AuthDriver=function(){function t(){}return t.prototype.authType=function(){return"code"},t.prototype.url=function(){return"https://some.url"},t.prototype.doAuthorize=function(t,e,r,n){return n({code:"access-code"})},t.prototype.getStateParam=function(t,e){return e(p.Util.Oauth.randomAuthStateParam())},t.prototype.resumeAuthorize=function(t,e,r){return r({code:"access-code"})},t.prototype.onAuthStateChange=function(t,e){return e()},t.oauthQueryParams=["access_token","expires_in","scope","token_type","code","error","error_description","error_uri","mac_key","mac_algorithm"].sort(),t}(),p.AuthDriver.autoConfigure=function(t){if("undefined"!=typeof chrome&&(chrome.extension||chrome.app&&chrome.app.runtime))return t.authDriver(new p.AuthDriver.Chrome),void 0;if("undefined"!=typeof window){if(window.cordova)return t.authDriver(new p.AuthDriver.Cordova),void 0;window&&window.navigator&&t.authDriver(new p.AuthDriver.Redirect)}},p.AuthDriver.BrowserBase=function(){function t(t){t?(this.rememberUser="rememberUser"in t?t.rememberUser:!0,this.scope=t.scope||"default"):(this.rememberUser=!0,this.scope="default"),this.storageKey=null,this.stateRe=/^[^#]+\#(.*&)?state=([^&]+)(&|$)/}return t.prototype.authType=function(){return"token"},t.prototype.onAuthStepChange=function(t,e){var r=this;switch(this.setStorageKey(t),t.authStep){case p.Client.RESET:return this.loadCredentials(function(n){return n?(t.setCredentials(n),t.authStep!==p.Client.DONE?e():r.rememberUser?(t.setCredentials(n),t.getAccountInfo(function(n){return n&&n.status===p.ApiError.INVALID_TOKEN?(t.reset(),r.forgetCredentials(e)):e()})):r.forgetCredentials(e)):e()});case p.Client.DONE:return this.rememberUser?this.storeCredentials(t.credentials(),e):this.forgetCredentials(e);case p.Client.SIGNED_OUT:return this.forgetCredentials(e);case p.Client.ERROR:return this.forgetCredentials(e);default:return e(),this}},t.prototype.setStorageKey=function(t){return this.storageKey="dropbox-auth:"+this.scope+":"+t.appHash(),this},t.prototype.storeCredentials=function(t,e){return localStorage.setItem(this.storageKey,JSON.stringify(t)),e(),this},t.prototype.loadCredentials=function(t){var e,r;if(r=localStorage.getItem(this.storageKey),!r)return t(null),this;try{t(JSON.parse(r))}catch(n){e=n,t(null)}return this},t.prototype.forgetCredentials=function(t){return localStorage.removeItem(this.storageKey),t(),this},t.prototype.locationStateParam=function(t){var e,r;return e=t||p.AuthDriver.BrowserBase.currentLocation(),r=this.stateRe.exec(e),r?decodeURIComponent(r[2]):null},t.prototype.replaceUrlBasename=function(t,e){var r,n,i;return n=t.indexOf("#"),-1!==n&&(t=t.substring(0,n)),i=t.indexOf("?"),-1!==i&&(t=t.substring(0,i)),r=t.split("/"),r[r.length-1]=e,r.join("/")},t.currentLocation=function(){return window.location.href},t.cleanupLocation=function(){var t,e;window.history&&window.history.replaceState?(e=this.currentLocation(),t=e.indexOf("#"),window.history.replaceState({},document.title,e.substring(0,t))):window.location.hash=""},t}(),p.AuthDriver.Redirect=function(t){function e(t){e.__super__.constructor.call(this,t),this.receiverUrl=this.baseUrl(t)}return ur(e,t),e.prototype.baseUrl=function(t){var e,r;if(r=p.AuthDriver.BrowserBase.currentLocation(),t){if(t.redirectUrl)return t.redirectUrl;if(t.redirectFile)return this.replaceUrlBasename(r,t.redirectFile)}return e=r.indexOf("#"),-1!==e&&(r=r.substring(0,e)),r},e.prototype.url=function(){return this.receiverUrl},e.prototype.doAuthorize=function(t,e,r){return this.storeCredentials(r.credentials(),function(){return window.location.assign(t)})},e.prototype.resumeAuthorize=function(t,e,r){var n;return this.locationStateParam()===t?(n=p.AuthDriver.BrowserBase.currentLocation(),p.AuthDriver.BrowserBase.cleanupLocation(),r(p.Util.Oauth.queryParamsFromUrl(n))):this.forgetCredentials(function(){return r({error:"Authorization error"})})},e}(p.AuthDriver.BrowserBase),p.AuthDriver.Popup=function(t){function e(t){e.__super__.constructor.call(this,t),this.receiverUrl=this.baseUrl(t)}return ur(e,t),e.prototype.url=function(){return this.receiverUrl},e.prototype.doAuthorize=function(t,e,r,n){return this.listenForMessage(e,n),this.openWindow(t)},e.prototype.baseUrl=function(t){var e;if(e=p.AuthDriver.BrowserBase.currentLocation(),t){if(t.receiverUrl)return t.receiverUrl;if(t.receiverFile)return this.replaceUrlBasename(e,t.receiverFile)}return e},e.prototype.openWindow=function(t){return window.open(t,"_dropboxOauthSigninWindow",this.popupWindowSpec(980,700))},e.prototype.popupWindowSpec=function(t,e){var r,n,i,o,s,a,u,l,h,c;return s=null!=(u=window.screenX)?u:window.screenLeft,a=null!=(l=window.screenY)?l:window.screenTop,o=null!=(h=window.outerWidth)?h:document.documentElement.clientWidth,r=null!=(c=window.outerHeight)?c:document.documentElement.clientHeight,n=Math.round(s+(o-t)/2),i=Math.round(a+(r-e)/2.5),s>n&&(n=s),a>i&&(i=a),"width="+t+",height="+e+","+("left="+n+",top="+i)+"dialog=yes,dependent=yes,scrollbars=yes,location=yes"},e.prototype.listenForMessage=function(t,e){var r,n=this;return r=function(i){var o,s,a;o=i.data?i.data:i;try{a=JSON.parse(o)._dropboxjs_oauth_info}catch(u){return s=u,void 0}if(a)return n.locationStateParam(a)===t?(t=!1,window.removeEventListener("message",r),p.AuthDriver.Popup.onMessage.removeListener(r),e(p.Util.Oauth.queryParamsFromUrl(o))):void 0},window.addEventListener("message",r,!1),p.AuthDriver.Popup.onMessage.addListener(r)},e.locationOrigin=function(t){var e;return(e=/^(file:\/\/[^\?\#]*)(\?|\#|$)/.exec(t))?e[1]:(e=/^([^\:]+\:\/\/[^\/\?\#]*)(\/|\?|\#|$)/.exec(t),e?e[1]:t)},e.oauthReceiver=function(){window.addEventListener("load",function(){var t,e,r,n,i,o;if(o=window.location.href,r=JSON.stringify({_dropboxjs_oauth_info:o}),p.AuthDriver.BrowserBase.cleanupLocation(),n=window.opener,window.parent!==window.top&&(n||(n=window.parent)),n){try{i=window.location.origin||locationOrigin(o),n.postMessage(r,i),window.close()}catch(s){e=s}try{return n.Dropbox.AuthDriver.Popup.onMessage.dispatch(r),window.close()}catch(s){t=s}}})},e.onMessage=new p.Util.EventSource,e}(p.AuthDriver.BrowserBase),d=null,f=null,"undefined"!=typeof chrome&&null!==chrome&&(chrome.runtime&&(chrome.runtime.onMessage&&(d=chrome.runtime.onMessage),chrome.runtime.sendMessage&&(f=function(t){return chrome.runtime.sendMessage(t)})),chrome.extension&&(chrome.extension.onMessage&&(d||(d=chrome.extension.onMessage)),chrome.extension.sendMessage&&(f||(f=function(t){return chrome.extension.sendMessage(t)}))),d||function(){var t,e;return e=function(t){return t.Dropbox?(p.AuthDriver.Chrome.prototype.onMessage=t.Dropbox.AuthDriver.Chrome.onMessage,p.AuthDriver.Chrome.prototype.sendMessage=t.Dropbox.AuthDriver.Chrome.sendMessage):(t.Dropbox=p,p.AuthDriver.Chrome.prototype.onMessage=new p.Util.EventSource,p.AuthDriver.Chrome.prototype.sendMessage=function(t){return p.AuthDriver.Chrome.prototype.onMessage.dispatch(t)})},chrome.extension&&chrome.extension.getBackgroundPage&&(t=chrome.extension.getBackgroundPage())?e(t):chrome.runtime&&chrome.runtime.getBackgroundPage?chrome.runtime.getBackgroundPage(function(t){return e(t)}):void 0}()),p.AuthDriver.Chrome=function(t){function e(t){var r;e.__super__.constructor.call(this,t),r=t&&t.receiverPath||"chrome_oauth_receiver.html",this.useQuery=!0,this.receiverUrl=this.expandUrl(r),this.storageKey="dropbox_js_"+this.scope+"_credentials"}return ur(e,t),e.prototype.onMessage=d,e.prototype.sendMessage=f,e.prototype.expandUrl=function(t){return chrome.runtime&&chrome.runtime.getURL?chrome.runtime.getURL(t):chrome.extension&&chrome.extension.getURL?chrome.extension.getURL(t):t},e.prototype.onAuthStepChange=function(t,e){var r=this;switch(t.authStep){case p.Client.RESET:return this.loadCredentials(function(n){if(n){if(n.authStep)return r.forgetCredentials(e);t.setCredentials(n)}return e()});case p.Client.DONE:return this.storeCredentials(t.credentials(),e);case p.Client.SIGNED_OUT:return this.forgetCredentials(e);case p.Client.ERROR:return this.forgetCredentials(e);default:return e()}},e.prototype.doAuthorize=function(t,e,r,n){var i,o,s,a,u=this;return(null!=(o=chrome.identity)?o.launchWebAuthFlow:void 0)?chrome.identity.launchWebAuthFlow({url:t,interactive:!0},function(t){return u.locationStateParam(t)===e?(e=!1,n(p.Util.Oauth.queryParamsFromUrl(t))):void 0}):(null!=(s=chrome.experimental)?null!=(a=s.identity)?a.launchWebAuthFlow:void 0:void 0)?chrome.experimental.identity.launchWebAuthFlow({url:t,interactive:!0},function(t){return u.locationStateParam(t)===e?(e=!1,n(p.Util.Oauth.queryParamsFromUrl(t))):void 0}):(i={handle:null},this.listenForMessage(e,i,n),this.openWindow(t,function(t){return i.handle=t}))},e.prototype.openWindow=function(t,e){return chrome.tabs&&chrome.tabs.create?(chrome.tabs.create({url:t,active:!0,pinned:!1},function(t){return e(t)}),this):this},e.prototype.closeWindow=function(t){return chrome.tabs&&chrome.tabs.remove&&t.id?(chrome.tabs.remove(t.id),this):chrome.app&&chrome.app.window&&t.close?(t.close(),this):this},e.prototype.url=function(){return this.receiverUrl},e.prototype.listenForMessage=function(t,e,r){var n,i=this;return n=function(o,s){var a;if((!s||!s.tab||s.tab.url.substring(0,i.receiverUrl.length)===i.receiverUrl)&&o.dropbox_oauth_receiver_href)return a=o.dropbox_oauth_receiver_href,i.locationStateParam(a)===t?(t=!1,e.handle&&i.closeWindow(e.handle),i.onMessage.removeListener(n),r(p.Util.Oauth.queryParamsFromUrl(a))):void 0},this.onMessage.addListener(n)},e.prototype.storeCredentials=function(t,e){var r;return r={},r[this.storageKey]=t,chrome.storage.local.set(r,e),this},e.prototype.loadCredentials=function(t){var e=this;return chrome.storage.local.get(this.storageKey,function(r){return t(r[e.storageKey]||null)}),this},e.prototype.forgetCredentials=function(t){return chrome.storage.local.remove(this.storageKey,t),this},e.oauthReceiver=function(){return window.addEventListener("load",function(){var t,e;return t=new p.AuthDriver.Chrome,e=window.location.href,window.location.hash="",t.sendMessage({dropbox_oauth_receiver_href:e}),window.close?window.close():void 0})},e}(p.AuthDriver.BrowserBase),p.AuthDriver.Cordova=function(t){function e(t){t?(this.rememberUser="rememberUser"in t?t.rememberUser:!0,this.scope=t.scope||"default"):(this.rememberUser=!0,this.scope="default"),this.scope=(null!=t?t.scope:void 0)||"default"}return ur(e,t),e.prototype.doAuthorize=function(t,e,r,n){var i,o,s,a;return o=window.open(t,"_blank","location=yes"),a=!1,i=/^[^/]*\/\/[^/]*\//.exec(t)[0],s=function(e){return e.url===t&&a===!1?(a=!0,void 0):e.url&&e.url.substring(0,i.length)!==i?(a=!1,void 0):"exit"===e.type||a?(o.removeEventListener("loadstop",s),o.removeEventListener("exit",s),"exit"!==e.type&&o.close(),n()):void 0},o.addEventListener("loadstop",s),o.addEventListener("exit",s)},e.prototype.url=function(){return null},e}(p.AuthDriver.BrowserBase),p.AuthDriver.NodeServer=function(){function t(t){this._port=(null!=t?t.port:void 0)||8912,(null!=t?t.tls:void 0)?(this._tlsOptions=t.tls,("string"==typeof this._tlsOptions||this._tlsOptions instanceof Buffer)&&(this._tlsOptions={key:this._tlsOptions,cert:this._tlsOptions})):this._tlsOptions=null,this._faviconFile=(null!=t?t.favicon:void 0)||null,this._fs=require("fs"),this._http=require("http"),this._https=require("https"),this._open=require("open"),this._callbacks={},this._nodeUrl=require("url"),this.createApp()}return t.prototype.authType=function(){return"code"},t.prototype.url=function(){return"https://localhost:"+this._port+"/oauth_callback"},t.prototype.doAuthorize=function(t,e,r,n){return this._callbacks[e]=n,this.openBrowser(t)},t.prototype.openBrowser=function(t){if(!t.match(/^https?:\/\//))throw new Error("Not a http/https URL: "+t);return"BROWSER"in process.env?this._open(t,process.env.BROWSER):this._open(t)},t.prototype.createApp=function(){var t=this;return this._app=this._tlsOptions?this._https.createServer(this._tlsOptions,function(e,r){return t.doRequest(e,r)}):this._http.createServer(function(e,r){return t.doRequest(e,r)}),this._app.listen(this._port)},t.prototype.closeServer=function(){return this._app.close()},t.prototype.doRequest=function(t,e){var r,n,i,o=this;return i=this._nodeUrl.parse(t.url,!0),"/oauth_callback"===i.pathname&&(n=i.query.state,this._callbacks[n]&&(this._callbacks[n](i.query),delete this._callbacks[n])),r="",t.on("data",function(t){return r+=t}),t.on("end",function(){return o._faviconFile&&"/favicon.ico"===i.pathname?o.sendFavicon(e):o.closeBrowser(e)})},t.prototype.closeBrowser=function(t){var e;return e='<!doctype html>\n<script type="text/javascript">window.close();</script>\n<p>Please close this window.</p>',t.writeHead(200,{"Content-Length":e.length,"Content-Type":"text/html"}),t.write(e),t.end()},t.prototype.sendFavicon=function(t){return this._fs.readFile(this._faviconFile,function(e,r){return t.writeHead(200,{"Content-Length":r.length,"Content-Type":"image/x-icon"}),t.write(r),t.end()})},t}(),p.AuthError=function(){function t(t){var e;if(!t.error)throw new Error("Not an OAuth 2.0 error: "+JSON.stringify(t));e="object"==typeof t.error&&t.error.error?t.error:t,this.code=e.error,this.description=e.error_description||null,this.uri=e.error_uri||null}return t.prototype.code=null,t.prototype.description=null,t.prototype.uri=null,t.ACCESS_DENIED="access_denied",t.INVALID_REQUEST="invalid_request",t.UNAUTHORIZED_CLIENT="unauthorized_client",t.INVALID_GRANT="invalid_grant",t.INVALID_SCOPE="invalid_scope",t.UNSUPPORTED_GRANT_TYPE="unsupported_grant_type",t.UNSUPPORTED_RESPONSE_TYPE="unsupported_response_type",t.SERVER_ERROR="server_error",t.TEMPORARILY_UNAVAILABLE="temporarily_unavailable",t.prototype.toString=function(){return"Dropbox OAuth error "+this.code+" :: "+this.description},t.prototype.inspect=function(){return this.toString()},t}(),p.Client=function(){function t(t){var e=this;this.serverRoot=t.server||this.defaultServerRoot(),this.maxApiServer="maxApiServer"in t?t.maxApiServer:this.defaultMaxApiServer(),this.authServer=t.authServer||this.defaultAuthServer(),this.fileServer=t.fileServer||this.defaultFileServer(),this.downloadServer=t.downloadServer||this.defaultDownloadServer(),this.onXhr=new p.Util.EventSource({cancelable:!0}),this.onError=new p.Util.EventSource,this.onAuthStepChange=new p.Util.EventSource,this.xhrOnErrorHandler=function(t,r){return e.handleXhrError(t,r)},this.oauth=new p.Util.Oauth(t),this.uid=t.uid||null,this.authStep=this.oauth.step(),this.driver=null,this.filter=null,this.authError=null,this._credentials=null,this._datastoreManager=null,this.setupUrls()}return t.prototype.onXhr=null,t.prototype.onError=null,t.prototype.onAuthStepChange=null,t.prototype.authDriver=function(t){return this.driver=t,this},t.prototype.dropboxUid=function(){return this.uid},t.prototype.credentials=function(){return this._credentials||this.computeCredentials(),this._credentials},t.prototype.authenticate=function(t,e){var r,n,i,o,s,a=this;if(e||"function"!=typeof t||(e=t,t=null),r=t&&"interactive"in t?t.interactive:!0,!this.driver&&this.authStep!==_.DONE&&(p.AuthDriver.autoConfigure(this),!this.driver))throw new Error("OAuth driver auto-configuration failed. Call authDriver.");if(this.authStep===_.ERROR)throw new Error("Client got in an error state. Call reset() to reuse it!");return o=function(){return a.authStep=a.oauth.step(),a.authStep===_.ERROR&&(a.authError=a.oauth.error()),a._credentials=null,a.onAuthStepChange.dispatch(a),s()},i=function(){return a.authStep=_.ERROR,a._credentials=null,a.onAuthStepChange.dispatch(a),s()},n=null,s=function(){var t;if(n!==a.authStep&&(n=a.authStep,a.driver&&a.driver.onAuthStepChange))return a.driver.onAuthStepChange(a,s),void 0;switch(a.authStep){case _.RESET:return r?(a.driver.getStateParam&&a.driver.getStateParam(function(t){return a.client.authStep===_.RESET&&a.oauth.setAuthStateParam(t),o()}),a.oauth.setAuthStateParam(p.Util.Oauth.randomAuthStateParam()),o()):(e&&e(null,a),void 0);case _.PARAM_SET:return r?(t=a.authorizeUrl(),a.driver.doAuthorize(t,a.oauth.authStateParam(),a,function(t){return a.oauth.processRedirectParams(t),t.uid&&(a.uid=t.uid),o()})):(e&&e(null,a),void 0);case _.PARAM_LOADED:return a.driver.resumeAuthorize?a.driver.resumeAuthorize(a.oauth.authStateParam(),a,function(t){return a.oauth.processRedirectParams(t),t.uid&&(a.uid=t.uid),o()}):(a.oauth.setAuthStateParam(a.oauth.authStateParam()),o(),void 0);case _.AUTHORIZED:return a.getAccessToken(function(t,e){return t?(a.authError=t,i()):(a.oauth.processRedirectParams(e),a.uid=e.uid,o())});case _.DONE:e&&e(null,a);break;case _.SIGNED_OUT:return a.authStep=_.RESET,a.reset(),s();case _.ERROR:e&&e(a.authError,a)}},s(),this},t.prototype.isAuthenticated=function(){return this.authStep===_.DONE},t.prototype.signOut=function(t,e){var r,n,i=this;if(e||"function"!=typeof t||(e=t,t=null),r=t&&t.mustInvalidate,this.authStep!==_.DONE)throw new Error("This client doesn't have a user's token");return n=new p.Util.Xhr("POST",this.urls.signOut),n.signWithOauth(this.oauth),this.dispatchXhr(n,function(t){if(t)if(t.status===p.ApiError.INVALID_TOKEN)t=null;else if(r)return e&&e(t),void 0;return i.authStep=_.RESET,i.reset(),i.authStep=_.SIGNED_OUT,i.onAuthStepChange.dispatch(i),i.driver&&i.driver.onAuthStepChange?i.driver.onAuthStepChange(i,function(){return e?e(null):void 0}):e?e(null):void 0})},t.prototype.signOff=function(t,e){return this.signOut(t,e)},t.prototype.getAccountInfo=function(t,e){var r,n;return e||"function"!=typeof t||(e=t,t=null),r=!1,t&&t.httpCache&&(r=!0),n=new p.Util.Xhr("GET",this.urls.accountInfo),n.signWithOauth(this.oauth,r),this.dispatchXhr(n,function(t,r){return e(t,p.AccountInfo.parse(r),r)})},t.prototype.getUserInfo=function(t,e){return this.getAccountInfo(t,e)},t.prototype.readFile=function(t,e,r){var n,i,o,s,a,u,l;return r||"function"!=typeof e||(r=e,e=null),i={},u="text",s=null,n=!1,e&&(e.versionTag?i.rev=e.versionTag:e.rev&&(i.rev=e.rev),e.arrayBuffer?u="arraybuffer":e.blob?u="blob":e.buffer?u="buffer":e.binary&&(u="b"),e.length?(null!=e.start?(a=e.start,o=e.start+e.length-1):(a="",o=e.length),s="bytes="+a+"-"+o):null!=e.start&&(s="bytes="+e.start+"-"),e.httpCache&&(n=!0)),l=new p.Util.Xhr("GET",""+this.urls.getFile+"/"+this.urlEncodePath(t)),l.setParams(i).signWithOauth(this.oauth,n),l.setResponseType(u),s&&(s&&l.setHeader("Range",s),l.reportResponseHeaders()),this.dispatchXhr(l,function(t,e,n,i){var o;return o=i?p.Http.RangeInfo.parse(i["content-range"]):null,r(t,e,p.File.Stat.parse(n),o)})},t.prototype.writeFile=function(t,e,r,n){var i;return n||"function"!=typeof r||(n=r,r=null),i=p.Util.Xhr.canSendForms&&"object"==typeof e,i?this.writeFileUsingForm(t,e,r,n):this.writeFileUsingPut(t,e,r,n)},t.prototype.writeFileUsingForm=function(t,e,r,n){var i,o,s,a;return s=t.lastIndexOf("/"),-1===s?(i=t,t=""):(i=t.substring(s),t=t.substring(0,s)),o={file:i},r&&(r.noOverwrite&&(o.overwrite="false"),r.lastVersionTag?o.parent_rev=r.lastVersionTag:(r.parentRev||r.parent_rev)&&(o.parent_rev=r.parentRev||r.parent_rev)),a=new p.Util.Xhr("POST",""+this.urls.postFile+"/"+this.urlEncodePath(t)),a.setParams(o).signWithOauth(this.oauth).setFileField("file",i,e,"application/octet-stream"),delete o.file,this.dispatchXhr(a,function(t,e){return n?n(t,p.File.Stat.parse(e)):void 0})},t.prototype.writeFileUsingPut=function(t,e,r,n){var i,o;return i={},r&&(r.noOverwrite&&(i.overwrite="false"),r.lastVersionTag?i.parent_rev=r.lastVersionTag:(r.parentRev||r.parent_rev)&&(i.parent_rev=r.parentRev||r.parent_rev)),o=new p.Util.Xhr("POST",""+this.urls.putFile+"/"+this.urlEncodePath(t)),o.setBody(e).setParams(i).signWithOauth(this.oauth),this.dispatchXhr(o,function(t,e){return n?n(t,p.File.Stat.parse(e)):void 0})},t.prototype.resumableUploadStep=function(t,e,r){var n,i;return e?(n={offset:e.offset},e.tag&&(n.upload_id=e.tag)):n={offset:0},i=new p.Util.Xhr("POST",this.urls.chunkedUpload),i.setBody(t).setParams(n).signWithOauth(this.oauth),this.dispatchXhr(i,function(t,e){return t&&t.status===p.ApiError.INVALID_PARAM&&t.response&&t.response.upload_id&&t.response.offset?r(null,p.Http.UploadCursor.parse(t.response)):r(t,p.Http.UploadCursor.parse(e))})},t.prototype.resumableUploadFinish=function(t,e,r,n){var i,o;return n||"function"!=typeof r||(n=r,r=null),i={upload_id:e.tag},r&&(r.lastVersionTag?i.parent_rev=r.lastVersionTag:(r.parentRev||r.parent_rev)&&(i.parent_rev=r.parentRev||r.parent_rev),r.noOverwrite&&(i.overwrite="false")),o=new p.Util.Xhr("POST",""+this.urls.commitChunkedUpload+"/"+this.urlEncodePath(t)),o.setParams(i).signWithOauth(this.oauth),this.dispatchXhr(o,function(t,e){return n?n(t,p.File.Stat.parse(e)):void 0})},t.prototype.stat=function(t,e,r){var n,i,o;return r||"function"!=typeof e||(r=e,e=null),i={},n=!1,e&&(e.versionTag?i.rev=e.versionTag:e.rev&&(i.rev=e.rev),e.contentHash?i.hash=e.contentHash:e.hash&&(i.hash=e.hash),(e.removed||e.deleted)&&(i.include_deleted="true"),e.readDir&&(i.list="true",e.readDir!==!0&&(i.file_limit=e.readDir.toString())),e.cacheHash&&(i.hash=e.cacheHash),e.httpCache&&(n=!0)),i.include_deleted||(i.include_deleted="false"),i.list||(i.list="false"),o=new p.Util.Xhr("GET",""+this.urls.metadata+"/"+this.urlEncodePath(t)),o.setParams(i).signWithOauth(this.oauth,n),this.dispatchXhr(o,function(t,e){var n,i,o;return o=p.File.Stat.parse(e),n=(null!=e?e.contents:void 0)?function(){var t,r,n,o;for(n=e.contents,o=[],t=0,r=n.length;r>t;t++)i=n[t],o.push(p.File.Stat.parse(i));return o}():void 0,r(t,o,n)})},t.prototype.readdir=function(t,e,r){var n;return r||"function"!=typeof e||(r=e,e=null),n={readDir:!0},e&&(null!=e.limit&&(n.readDir=e.limit),e.versionTag?n.versionTag=e.versionTag:e.rev&&(n.versionTag=e.rev),e.contentHash?n.contentHash=e.contentHash:e.hash&&(n.contentHash=e.hash),(e.removed||e.deleted)&&(n.removed=e.removed||e.deleted),e.httpCache&&(n.httpCache=e.httpCache)),this.stat(t,n,function(t,e,n){var i,o;return i=n?function(){var t,e,r;for(r=[],t=0,e=n.length;e>t;t++)o=n[t],r.push(o.name);return r}():null,r(t,i,e,n)})},t.prototype.metadata=function(t,e,r){return this.stat(t,e,r)},t.prototype.makeUrl=function(t,e,r){var n,i,o,s,a,u=this;return r||"function"!=typeof e||(r=e,e=null),i=e&&(e["long"]||e.longUrl||e.downloadHack)?{short_url:"false"}:{},t=this.urlEncodePath(t),o=""+this.urls.shares+"/"+t,n=!1,s=!1,e&&(e.downloadHack?(n=!0,s=!0):e.download&&(n=!0,o=""+this.urls.media+"/"+t)),a=new p.Util.Xhr("POST",o).setParams(i).signWithOauth(this.oauth),this.dispatchXhr(a,function(t,e){return s&&(null!=e?e.url:void 0)&&(e.url=e.url.replace(u.authServer,u.downloadServer)),r(t,p.File.ShareUrl.parse(e,n))})},t.prototype.history=function(t,e,r){var n,i,o;return r||"function"!=typeof e||(r=e,e=null),i={},n=!1,e&&(null!=e.limit&&(i.rev_limit=e.limit),e.httpCache&&(n=!0)),o=new p.Util.Xhr("GET",""+this.urls.revisions+"/"+this.urlEncodePath(t)),o.setParams(i).signWithOauth(this.oauth,n),this.dispatchXhr(o,function(t,e){var n,i;return i=e?function(){var t,r,i;for(i=[],t=0,r=e.length;r>t;t++)n=e[t],i.push(p.File.Stat.parse(n));return i}():void 0,r(t,i)})},t.prototype.revisions=function(t,e,r){return this.history(t,e,r)},t.prototype.thumbnailUrl=function(t,e){var r;return r=this.thumbnailXhr(t,e),r.paramsToUrl().url},t.prototype.readThumbnail=function(t,e,r){var n,i;return r||"function"!=typeof e||(r=e,e=null),n="b",e&&(e.blob&&(n="blob"),e.arrayBuffer&&(n="arraybuffer"),e.buffer&&(n="buffer")),i=this.thumbnailXhr(t,e),i.setResponseType(n),this.dispatchXhr(i,function(t,e,n){return r(t,e,p.File.Stat.parse(n))})},t.prototype.thumbnailXhr=function(t,e){var r,n;return r={},e&&(e.format?r.format=e.format:e.png&&(r.format="png"),e.size&&(r.size=e.size)),n=new p.Util.Xhr("GET",""+this.urls.thumbnails+"/"+this.urlEncodePath(t)),n.setParams(r).signWithOauth(this.oauth)},t.prototype.revertFile=function(t,e,r){var n;return n=new p.Util.Xhr("POST",""+this.urls.restore+"/"+this.urlEncodePath(t)),n.setParams({rev:e}).signWithOauth(this.oauth),this.dispatchXhr(n,function(t,e){return r?r(t,p.File.Stat.parse(e)):void 0})},t.prototype.restore=function(t,e,r){return this.revertFile(t,e,r)},t.prototype.findByName=function(t,e,r,n){var i,o,s;return n||"function"!=typeof r||(n=r,r=null),o={query:e},i=!1,r&&(null!=r.limit&&(o.file_limit=r.limit),(r.removed||r.deleted)&&(o.include_deleted=!0),r.httpCache&&(i=!0)),s=new p.Util.Xhr("GET",""+this.urls.search+"/"+this.urlEncodePath(t)),s.setParams(o).signWithOauth(this.oauth,i),this.dispatchXhr(s,function(t,e){var r,i;return i=e?function(){var t,n,i;for(i=[],t=0,n=e.length;n>t;t++)r=e[t],i.push(p.File.Stat.parse(r));return i}():void 0,n(t,i)})},t.prototype.search=function(t,e,r,n){return this.findByName(t,e,r,n)},t.prototype.makeCopyReference=function(t,e){var r;return r=new p.Util.Xhr("GET",""+this.urls.copyRef+"/"+this.urlEncodePath(t)),r.signWithOauth(this.oauth),this.dispatchXhr(r,function(t,r){return e(t,p.File.CopyReference.parse(r))})},t.prototype.copyRef=function(t,e){return this.makeCopyReference(t,e)},t.prototype.pullChanges=function(t,e){var r,n;return e||"function"!=typeof t||(e=t,t=null),r=t?t.cursorTag?{cursor:t.cursorTag}:{cursor:t}:{},n=new p.Util.Xhr("POST",this.urls.delta),n.setParams(r).signWithOauth(this.oauth),this.dispatchXhr(n,function(t,r){return e(t,p.Http.PulledChanges.parse(r))})},t.prototype.delta=function(t,e){return this.pullChanges(t,e)},t.prototype.mkdir=function(t,e){var r;return r=new p.Util.Xhr("POST",this.urls.fileopsCreateFolder),r.setParams({root:"auto",path:this.normalizePath(t)}).signWithOauth(this.oauth),this.dispatchXhr(r,function(t,r){return e?e(t,p.File.Stat.parse(r)):void 0})},t.prototype.remove=function(t,e){var r;return r=new p.Util.Xhr("POST",this.urls.fileopsDelete),r.setParams({root:"auto",path:this.normalizePath(t)}).signWithOauth(this.oauth),this.dispatchXhr(r,function(t,r){return e?e(t,p.File.Stat.parse(r)):void 0})},t.prototype.unlink=function(t,e){return this.remove(t,e)},t.prototype["delete"]=function(t,e){return this.remove(t,e)},t.prototype.copy=function(t,e,r){var n,i,o;return r||"function"!=typeof n||(r=n,n=null),i={root:"auto",to_path:this.normalizePath(e)},t instanceof p.File.CopyReference?i.from_copy_ref=t.tag:i.from_path=this.normalizePath(t),o=new p.Util.Xhr("POST",this.urls.fileopsCopy),o.setParams(i).signWithOauth(this.oauth),this.dispatchXhr(o,function(t,e){return r?r(t,p.File.Stat.parse(e)):void 0})},t.prototype.move=function(t,e,r){var n,i;return r||"function"!=typeof n||(r=n,n=null),i=new p.Util.Xhr("POST",this.urls.fileopsMove),i.setParams({root:"auto",from_path:this.normalizePath(t),to_path:this.normalizePath(e)}).signWithOauth(this.oauth),this.dispatchXhr(i,function(t,e){return r?r(t,p.File.Stat.parse(e)):void 0})},t.prototype.reset=function(){var t;return this.uid=null,this.oauth.reset(),t=this.authStep,this.authStep=this.oauth.step(),t!==this.authStep&&this.onAuthStepChange.dispatch(this),this.authError=null,this._credentials=null,this},t.prototype.setCredentials=function(t){var e;return e=this.authStep,this.oauth.setCredentials(t),this.authStep=this.oauth.step(),this.uid=t.uid||null,this.authError=null,this._credentials=null,e!==this.authStep&&this.onAuthStepChange.dispatch(this),this},t.prototype.appHash=function(){return this.oauth.appHash()},t.prototype.setupUrls=function(){return this.apiServer=this.chooseApiServer(),this.urls={authorize:""+this.authServer+"/1/oauth2/authorize",token:""+this.apiServer+"/1/oauth2/token",signOut:""+this.apiServer+"/1/unlink_access_token",accountInfo:""+this.apiServer+"/1/account/info",getFile:""+this.fileServer+"/1/files/auto",postFile:""+this.fileServer+"/1/files/auto",putFile:""+this.fileServer+"/1/files_put/auto",metadata:""+this.apiServer+"/1/metadata/auto",delta:""+this.apiServer+"/1/delta",revisions:""+this.apiServer+"/1/revisions/auto",restore:""+this.apiServer+"/1/restore/auto",search:""+this.apiServer+"/1/search/auto",shares:""+this.apiServer+"/1/shares/auto",media:""+this.apiServer+"/1/media/auto",copyRef:""+this.apiServer+"/1/copy_ref/auto",thumbnails:""+this.fileServer+"/1/thumbnails/auto",chunkedUpload:""+this.fileServer+"/1/chunked_upload",commitChunkedUpload:""+this.fileServer+"/1/commit_chunked_upload/auto",fileopsCopy:""+this.apiServer+"/1/fileops/copy",fileopsCreateFolder:""+this.apiServer+"/1/fileops/create_folder",fileopsDelete:""+this.apiServer+"/1/fileops/delete",fileopsMove:""+this.apiServer+"/1/fileops/move",getDb:""+this.apiServer+"/r5/datastores/get_db",getOrCreateDb:""+this.apiServer+"/r5/datastores/get_or_create_db",listDbs:""+this.apiServer+"/r5/datastores/list_dbs",deleteDb:""+this.apiServer+"/r5/datastores/delete_db",getSnapshot:""+this.apiServer+"/r5/datastores/get_snapshot",getDeltas:""+this.apiServer+"/r5/datastores/get_deltas",putDelta:""+this.apiServer+"/r5/datastores/put_delta",awaitDeltas:""+this.apiServer+"/r5/datastores/await_deltas",datastoreAwait:""+this.apiServer+"/r5/datastores/await"},this
},t.prototype.chooseApiServer=function(){var t,e;return e=Math.floor(Math.random()*(this.maxApiServer+1)),t=0===e?"":e.toString(),this.serverRoot.replace("$",t)},t.prototype.authStep=null,t.ERROR=0,t.RESET=1,t.PARAM_SET=2,t.PARAM_LOADED=3,t.AUTHORIZED=4,t.DONE=5,t.SIGNED_OUT=6,t.prototype.urlEncodePath=function(t){return p.Util.Xhr.urlEncodeValue(this.normalizePath(t)).replace(/%2F/gi,"/")},t.prototype.normalizePath=function(t){var e;if("/"===t.substring(0,1)){for(e=1;"/"===t.substring(e,e+1);)e+=1;return t.substring(e)}return t},t.prototype.authorizeUrl=function(){var t;return t=this.oauth.authorizeUrlParams(this.driver.authType(),this.driver.url()),this.urls.authorize+"?"+p.Util.Xhr.urlEncode(t)},t.prototype.getAccessToken=function(t){var e,r;return e=this.oauth.accessTokenParams(this.driver.url()),r=new p.Util.Xhr("POST",this.urls.token).setParams(e).addOauthParams(this.oauth),this.dispatchXhr(r,function(e,r){return e&&e.status===p.ApiError.INVALID_PARAM&&e.response&&e.response.error&&(e=new p.AuthError(e.response)),t(e,r)})},t.prototype.dispatchLongPollXhr=function(t,e,r){return null==r&&(r=6e4),this.dispatchXhr(t,e,r)},t.prototype.dispatchXhr=function(t,e,r){var n,i,o=this;return null==r&&(r=1e4),n=setTimeout(function(){return o.handleLongRequest(t)},2*r),t.setCallback(function(t,r,i,o){return clearTimeout(n),e(t,r,i,o)}),t.onError=this.xhrOnErrorHandler,t.prepare(),i=t.xhr,this.onXhr.dispatch(t)&&t.send(),i},t.prototype.handleXhrError=function(t,e){var r=this;return t.status===p.ApiError.INVALID_TOKEN&&this.authStep===_.DONE&&(this.authError=t,this.authStep=_.ERROR,this.onAuthStepChange.dispatch(this),this.driver&&this.driver.onAuthStepChange)?(this.driver.onAuthStepChange(this,function(){return r.onError.dispatch(t),e(t)}),null):(this.onError.dispatch(t),e(t),void 0)},t.prototype.handleLongRequest=function(){return this.setupUrls()},t.prototype.defaultServerRoot=function(){return"https://api$.dropbox.com"},t.prototype.defaultAuthServer=function(){return this.serverRoot.replace("api$","www")},t.prototype.defaultFileServer=function(){return this.serverRoot.replace("api$","api-content")},t.prototype.defaultDownloadServer=function(){return this.serverRoot.replace("api$","dl")},t.prototype.defaultMaxApiServer=function(){return 30},t.prototype.computeCredentials=function(){var t;t=this.oauth.credentials(),this.uid&&(t.uid=this.uid),this.serverRoot!==this.defaultServerRoot()&&(t.server=this.serverRoot),this.maxApiServer!==this.defaultMaxApiServer()&&(t.maxApiServer=this.maxApiServer),this.authServer!==this.defaultAuthServer()&&(t.authServer=this.authServer),this.fileServer!==this.defaultFileServer()&&(t.fileServer=this.fileServer),this.downloadServer!==this.defaultDownloadServer()&&(t.downloadServer=this.downloadServer),this._credentials=t},t}(),_=p.Client,p.Datastore=function(t){function e(t,r,n,i){var o=this;this._datastore_manager=t,this._managed_datastore=r,this._dsid=n,this._path=i,e.__super__.constructor.call(this),this._record_cache=new I(this),this._last_used_timestamp=0,this.recordsChanged=new p.Util.EventSource,this.syncStatusChanged=new p.Util.EventSource,this._timeoutWrapper=function(t){return t},this._evt_mgr=new D,this._evt_mgr.register(this._managed_datastore,"sync-state-changed",function(){return o._syncSoon(),o.dispatch("sync-status-changed",null),o.syncStatusChanged.dispatch(null)}),this._syncPending=!1,this._closed=!1}return ur(e,t),e.prototype.recordsChanged=null,e.prototype.syncStatusChanged=null,e.openDefault=function(t,e){return t.openDefaultDatastore(e),this},e.int64=function(t){var e,r;if(be(t)&&null!=t[C])return er(t);if(Se(t)){if(!xe(t))throw new Error("Not a valid int64 in string form: "+t);return r=new Number(parseInt(t,10)),r[C]=t,er(r)}if(!be(t)||!isFinite(t))throw new Error("Not a finite number: "+t);if(Number(t)!==Math.round(t))throw new Error("Number is not an integer: "+t);if(e=t.toFixed(),!xe(e))throw new Error("Number not in int64 range: "+t);return r=new Number(t),r[C]=e,er(r)},e.isInt64=function(t){return ve(t)},e.prototype.getTable=function(t){if(this._checkNotClosed(),!p.Datastore.Table.isValidId(t))throw new Error("Invalid table ID: "+t);return new p.Datastore.Table(this,t)},e.prototype.listTableIds=function(){return this._checkNotClosed(),this._managed_datastore.list_tables()},e.prototype.toString=function(){var t;return t=this._closed?"[closed] ":"","Dropbox.Datastore("+t+this._path+")"},e.prototype.close=function(){return this._closed=!0,this._evt_mgr.unregister_all(),this._listeners=[],this._datastore_manager._datasync.obj_manager.close(this._dsid),void 0},e.prototype.getId=function(){return this._path},e.prototype.getSyncStatus=function(){return{uploading:this._managed_datastore.get_outgoing_delta_count()>0}},e.isValidId=function(t){var e;return e=new RegExp("^[-._=0-9a-zA-Z]{1,32}$"),Se(t)&&e.test(t)?"."!==t.substring(0,1)&&"."!==t.substring(t.length-1):!1},e.prototype._generateRid=function(){var t,e,r,n;for(n="_",e="_js_",r=Math.round(1e3*Date.now()),r<=this._last_used_timestamp&&(r=this._last_used_timestamp+1),this._last_used_timestamp=r,t=r.toString(32);t.length<11;)t="0"+t;return n+t+e+Me(5)},e.prototype._syncSoon=function(){var t=this;if(this._managed_datastore.is_deleted())throw new Error("Cannot sync deleted datastore "+this._path+".");return this._checkNotClosed(),this._syncPending||(this._syncPending=!0,setTimeout(this._timeoutWrapper(function(){return t._syncPending=!1,t._sync()}),0)),void 0},e.prototype._sync=function(){var t,e,r,n,i,o,s,a,u;this._checkNotClosed(),i=this._managed_datastore.sync(),n=this._resolveAffectedRecordMap(i),t=!1;for(s in n)for(r=n[s],a=0,u=r.length;u>a;a++)e=r[a],W(s===e._tid,"tid mismatch"),t=!0,o=e._rid,this._managed_datastore.query(s,o)||(e._deleted=!0,this._record_cache.remove(s,o));return t&&(this.dispatch("records-changed",new L(n,!1)),this.recordsChanged.dispatch(new L(n,!1))),void 0},e.prototype._resolveAffectedRecordMap=function(t){var e,r,n,i,o;r={};for(o in t){i=t[o];for(n in i)e=this._record_cache.getOrCreate(o,n),null==r[o]&&(r[o]=[]),r[o].push(e)}return r},e.prototype._recordsChangedLocally=function(t){return t.length>0&&(this.dispatch("records-changed",L._fromRecordList(t,!0)),this.recordsChanged.dispatch(L._fromRecordList(t,!0)),this._syncSoon()),void 0},e.prototype._checkNotClosed=function(){if(this._closed||!this._managed_datastore._open)throw new Error("Datastore is already closed: "+this);return void 0},e}(p.Util.TypedEventSource),ce=p.Datastore.int64,he=p.Datastore.impl={},M=p.Datastore.impl.T={},le=function(t){return t},M.get_coerce_fn=function(t){return null!=t.coerce?t.coerce:null!=t.load_json?function(e){return e instanceof t?e:t.load_json(e)}:le},M.get_T_fn=function(t){return null!=t.Type?t.Type:t},Ve=function(t){return M.is_string(t)?t:"function"==typeof t?t():JSON.stringify(t)},M.assert=function(t,e){if(!t)throw new Error(Ve(e))},W=M.assert,M.check=function(t,e,r,n,i,o){if(t)return r;throw M.fail(e,r,n,i,o),new Error("unreachable")},se="[object Object]",M.safe_to_string=function(t){var e,r;try{if(r=t.toString(),r!==se)return r}catch(n){e=n}try{return JSON.stringify(t)}catch(n){e=n}try{if(r=t.constructor.name,null!=r?r.match(/^[A-Za-z0-9_]+$/):void 0)return r}catch(n){e=n}return"[T.safe_to_string failed]"},M.fail=function(t,e,r,n,i){var o,s;throw s=null!=r?null!=n?null!=i?"Wanted "+Ve(n)+", but "+Ve(r)+" in "+Ve(i)+" "+Ve(t):"Wanted "+Ve(n)+", but "+Ve(r)+" "+Ve(t):""+Ve(r)+" "+Ve(t):null!=n?null!=i?"Wanted "+Ve(n)+", but in "+Ve(i)+" "+Ve(t):"Wanted "+Ve(n)+", but "+t:""+Ve(t),o=new Error(""+s+": "+M.safe_to_string(e)),console.error(o),o},M.any=function(t){return t},M.defined=function(t,e,r,n){return null==r&&(r="defined"),M.check("undefined"!=typeof t,"is undefined",t,e,r,n),t},M.nonnull=function(t,e,r,n){return null==r&&(r="nonnull"),M.defined(t,e,r,n),M.check(null!=t,"is null",t,e,r,n),t},M.member=function(t){var e,r;return r="value in "+JSON.stringify(t),e="not in "+JSON.stringify(t),function(n,i,o,s){return null==o&&(o=r),M.check(sr.call(t,n)>=0,e,n,i,o,s)}},M.object=function(t,e,r,n){return null==r&&(r="object"),M.nonnull(t,e,r,n),M.check("object"==typeof t,"not an object",t,e,r,n),t},M.bool=function(t,e,r,n){return null==r&&(r="bool"),M.nonnull(t,e,r,n),M.check(t===!0||t===!1,"is not bool",t,e,r,n),t},M.string=function(t,e,r,n){return null==r&&(r="string"),M.nonnull(t,e,r,n),M.check(M.is_string(t),"is not a string",t,e,r,n),t},M.num=function(t,e,r,n){return null==r&&(r="num"),M.nonnull(t,e,r,n),M.check("number"==typeof t,"is not numeric",t,e,r,n),t},M.int=function(t,e,r,n){return null==r&&(r="int"),M.num(t,e,r,n),M.check(0===t%1,"is not an integer",t,e,r,n),t},M.uint=function(t,e,r,n){return null==r&&(r="uint"),M.int(t,e,r,n),M.check(t>=0,"is negative",t,e,r,n),t},M.nullable=function(t){var e,r;return r="nullable("+t+")",e=function(e,n,i,o){return null==i&&(i=function(){return r}),M.defined(e,n,i,o),null!=e&&M.get_T_fn(t)(e,n,i,o),e},e.toString=function(){return r},e.coerce=function(e){return null!=e?M.get_coerce_fn(t)(e):null},e},M.array=function(t,e,r,n){return null==r&&(r="array"),M.nonnull(t,e,r,n),M.check(M.is_array(t),"is not an array",t,e,r,n),t},M.arrayOf=function(t){var e,r;return r="arrayOf("+t+")",e=function(e,n,i,o){var s,a,u,l,h;for(null==i&&(i=r),M.array(e,n,i,o),u=l=0,h=e.length;h>l;u=++l)s=e[u],a=function(){return null!=n?"element "+u+" of "+Ve(n):"element "+u},M.get_T_fn(t)(s,a,i,o);return e},e.toString=function(){return r},e.coerce=function(e){var r,n,i,o;for(o=[],n=0,i=e.length;i>n;n++)r=e[n],o.push(M.get_coerce_fn(t)(r));return o},e},M.instance=function(t,e,r,n,i){var o;if(!(e instanceof Function))throw new Error("Invalid type given: "+e);return t instanceof e||(null==n&&(n=e.name),M.check(!1,"got instance of "+(null!=t?null!=(o=t.constructor)?o.name:void 0:void 0),t,r,n,i)),t},M.unimplemented=function(t){return function(){throw new Error("unimplemented "+t)}},We=function(t,e){return 0===t.lastIndexOf(e,0)},Ke=function(t,e,r,n,i){return M.string(e,r,n,i),We(e,t)||M.fail("does not start with "+t,e,r,n,i),e},Ge=function(t,e,r,n,i,o){var s,a,u,l,h;for(Ke(t,r,n,i,o),s=u=l=t.length,h=r.length;h>=l?h>u:u>h;s=h>=l?++u:--u)e.indexOf(r[s])<0&&(a=t.length>0?"does not consist of "+e+" after prefix "+t:"does not consist of "+e,M.fail(a,r,n,i,o));return r},M.string_matching=function(t){var e;return M.string(t),M.check(/^[^].*[$]$/.test(t),"does not start with ^ and end with $",t),e="does not match regex "+t,function(r,n,i,o){return M.string(r,n,i,o),M.check(new RegExp(t).test(r),e,r,n,i,o),r}},o="0123456789",X="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_",M.is_a=function(t){var e;if(!t.dump_json&&null==t.prototype.toJSON)throw new Error("Can't make T element from type "+t+", missing dump_json or toJSON");return e=function(e,r,n,i){var o;return e instanceof t||(o=t.toString(),o.length>50&&(o=o.substring(0,50)+"..."),M.fail('is not of type "'+o+'"',e,r,n,i)),e},e.coerce=function(e){var r,n;return r=M.get_coerce_fn(t)(e),r.toJSON=null!=(n=t.prototype.toJSON)?n:function(){return t.dump_json(this)},r},e},M.is_defined=function(t){return"undefined"!=typeof t},M.is_bool=function(t){return t===!0||t===!1},M.is_number=function(t){return"number"==typeof t||t&&"object"==typeof t&&t.constructor===Number},M.is_json_number=function(t){return M.is_number(t)&&!isNaN(t)&&isFinite(t)},M.is_string=function(t){return"string"==typeof t||t&&"object"==typeof t&&t.constructor===String},M.is_array=function(t){return"[object Array]"===Object.prototype.toString.call(t)},M.is_empty=function(t){return 0===Object.keys(t).length},M.is_uid=function(t){return M.is_string(t)&&null!=t.match(/^u[0-9]*$/)},M.is_nid=function(t){return M.is_string(t)&&null!=t.match(/^n[0-9]*$/)},M.is_db_path=function(t){return M.is_string(t)&&null!=t.match(/^[-_.a-z0-9]{1,32}$/)&&"."!==t[0]&&"."!==t[t.length-1]},M.dbid_from_nid=function(t){return M.nid(t),M.assert(t[0]="n",function(){return"bad nid: "+t}),M.dbid("00"+t.slice(1))},M.uid=function(t,e,r,n){return null==r&&(r="uid"),Ge("u",o,t,e,r,n),t},M.cid=function(t,e,r,n){return null==r&&(r="cid"),t.match(/^c[0-9]+_u[0-9]*$/)?t:(Ge("c",o,t,e,r,n),t)},M.nid=function(t,e,r,n){return null==r&&(r="nid"),M.string_matching("^n[0-9]{1,10}$")(t,e,r,n),t},M.is_simple_map=function(t){var e,r;if(null==t||"object"!=typeof t)return!1;for(e in t)if(r=t[e],!Object.prototype.hasOwnProperty.call(t,e))return!1;return!0},M.simple_map=function(t,e,r,n){var i,o;null==r&&(r="simple map"),M.object(t,e,r,n);for(i in t)o=t[i],M.check(Object.prototype.hasOwnProperty.call(t,i),function(){return"property "+i+" is inherited"},t,e,r,t);return t},M.simple_typed_map=function(t,e,r){var n,i,o;return n=M.get_coerce_fn(e),i=M.get_coerce_fn(r),o=function(n,i,o,s){var a,u;null==o&&(o=t),M.simple_map(n,i,o,s);for(a in n)u=n[a],M.get_T_fn(e)(a,"property",null,n),M.get_T_fn(r)(u,function(){return"value of property "+a},null,n);return n},o.coerce=function(e){var r,o,s;M.simple_map(e,null,t),o={};for(r in e)s=e[r],o[n(r)]=i(s);return o},o},M.db_path=function(t,e,r,n){return null==r&&(r="db_path"),M.check(M.is_db_path(t),"is not a valid db path",e,r,n),t},M.dbid=function(t,e,r,n){return null==r&&(r="dbid"),M.string(t,e,r,n),t},M.delta_nonce=function(t,e,r,n){return null==r&&(r="delta_nonce"),M.string_matching("^[-_0-9a-zA-Z]{0,30}$")(t,e,r,n),t},M.delta_metadata=function(t,e,r,n){return null==r&&(r="delta_metadata"),M.string(t,e,r,n),t},qe="^[-._+/=0-9a-zA-Z]{1,32}$",M.tid=function(t,e,r,n){return null==r&&(r="tid"),M.string_matching(qe)(t,e,r,n),t},M.rowid=function(t,e,r,n){return null==r&&(r="rowid"),M.string_matching(qe)(t,e,r,n),t},M.field_name=function(t,e,r,n){return null==r&&(r="field name"),M.string_matching(qe)(t,e,r,n),t},M.appid=function(t,e,r,n){return null==r&&(r="appid"),M.string_matching("^[0-9]{1,15}$")(t,e,r,n),t},M.floid=function(t,e,r,n){return null==r&&(r="floid"),M.nid(t,e,r,n),t},M.flobid=function(t,e,r,n){return M.dbid(t,e,null!=r?r:"flobid",n)},M.share_token=function(t,e,r,n){return null==r&&(r="share_token"),Ge("s",X,t,e,r,n),t},M.email=function(t,e,r,n){return null==r&&(r="email"),M.string(t,e,r,n),M.check(t.indexOf(!0),"contains no @",e,r,n),t},M.uid_from_db_uid=function(t){return M.uid("u"+M.int(t))},ir=function(t){return M.hasOwnProperty(t)?tr.toString=function(){return"T."+t}:void 0};for(Ce in M)tr=M[Ce],ir(Ce);if($e={},$e.define=function(t,e){var r,n,i,o,s,a,u,l,h,c,p,d,f,_,y;for(M.string(t,"struct name"),M.array(e,"fields"),a=[],s={},u=_=0,y=e.length;y>_;u=++_){i=e[u],M.array(i,"field","field descriptor",e),M.check(2<=i.length&&i.length<=3,"does not have length 2 or 3",i,"field descriptor"),p=M.string(i[0],"field name","field descriptor",e),f=M.nonnull(i[1],"field type","field descriptor",e),d=i.length<=2?{}:M.nonnull(i[2],"map of field options","field descriptor",e);for(Ce in d)"init"!==Ce&&"initFn"!==Ce&&M.fail("unknown option "+Ce,d,"field options","field descrptor",e);sr.call(d,"init")>=0&&sr.call(d,"initFn")>=0&&M.fail("both 'init' and 'initFn' specified",d,"field options","field descriptor",e),h="initFn"in d?d.initFn:"init"in d?(l=d.init,function(t){return function(){return t}}(l)):null,r={name:p,type:f,initFn:h},o="undefined"!=typeof N&&null!==N?new N(r):r,a.push(o),s[p]=o}return c="initializer for "+t+" (fields "+function(){var t,e,r;for(r=[],t=0,e=a.length;e>t;t++)i=a[t],r.push(i.name);return r}().join(", ")+")",n=function(t){var e,r,i;M.defined(t,"x","initializer");for(p in t)e=t[p],t.hasOwnProperty(p)&&M.check(null!=s[p],function(){return"has an unexpected field "+p},t,"initializer");for(r=0,i=a.length;i>r;r++)o=a[r],t[o.name]&&!t.hasOwnProperty(o.name)&&M.fail("Has an indirect property "+o.name,t,"initializer"),t.hasOwnProperty(o.name)?(e=t[o.name],this[o.name]=M.get_coerce_fn(o.type)(e)):null!=o.initFn?this[o.name]=o.initFn():M.fail("lacks the field "+o.name,t,"initializer");return n.Type(this,"initializer",c,this),this},n.Type=function(e,r,i,u){var l,h,c;for(M.defined(e,r,i,u),M.check(e instanceof n,function(){return"is not an instance of "+t},e,r,i,u),h=0,c=a.length;c>h;h++)o=a[h],M.check(e.hasOwnProperty(o.name),function(){return"lacks the field "+o.name},e,r,i,u),M.get_T_fn(o.type)(e[o.name],o.name,i,u);for(p in e)l=e[p],e.hasOwnProperty(p)&&M.check(null!=s[p],"has an unexpected field",p,r,i,u);return e},n.coerce=function(t){return t instanceof n?(n.Type(t),t):new n(t)},n.prototype.toString=function(){var t,e;return e=this,t=function(){var t,r,n;for(n=[],t=0,r=a.length;r>t;t++)o=a[t],n.push(""+o.name+": "+JSON.stringify(e[o.name]));return n}(),"{"+t.join(", ")+"}"},n.prototype.toJSON=function(){var t,e,r;for(t=this,Ve=function(){return""+t},e=0,r=a.length;r>e;e++)o=a[e],M.get_T_fn(o.type)(this[o.name],o.name,null,Ve);return this},n.fromJSON=function(e){var r,i;M.string(e,"input"),i=JSON.parse(e),r=[];for(Ce in i)tr=i[Ce],null==s[Ce]&&(r.push(""+Ce+": "+JSON.stringify(tr)),delete i[Ce]);return r.length>0&&console.info("Ignoring unknown fields while deserializing "+t+": "+r.join(", ")),new n(i)},n.toString=function(){return"struct "+t},n},N=$e.define("StructField",[["name",M.string],["type",M.defined],["initFn",M.defined]]),$e.toJSO=function(t){var e,r;if("object"!=typeof t)return t;if(M.is_array(t))return function(){var r,n,i;for(i=[],r=0,n=t.length;n>r;r++)e=t[r],i.push($e.toJSO(e));return i}();r={};for(Ce in t)tr=t[Ce],t.hasOwnProperty(Ce)&&(r[Ce]=$e.toJSO(tr));return r},$e.union_as_list=function(t,e){var r,n,i,o,s,a,u,l,h,c;for(M.string(t,"union name"),M.array(e,"variants"),a=function(){throw new Error("Use "+t+".from_array instead")},u={},s=[],l=function(e,r,n){var i;return i=$e.define(""+t+"."+e,n),i.prototype.tag=function(){return e},i.prototype.toString=function(){return""+t+"."+e+"("+JSON.stringify(this)+")"},i.prototype.toJSON=function(){var t,n,i,o,s,a;for(t=[e],s=0,a=r.length;a>s;s++)n=r[s],i=n[0],o=n[1],M.get_T_fn(o)(this[i],i),t.push(this[i]);return t},i.from_array=function(n){var o,s,a,u,l,h,c;for(l="initializer for "+t,M.array(n,"initializer",l),M.check(n.length===r.length+1,"does not have length "+(r.length+1),n,"initializer",l),M.check(n[0]===e,"does not have tag "+e,n,"initializer",l),o={_tag:e},a=h=0,c=r.length;c>h;a=++h)s=r[a],u=s[0],o[u]=n[a+1];return new i(o)},i.coerce=function(t){return t instanceof i?(i.Type(t),t):i.from_array(t)},u[e]=i,a[e]=i},h=0,c=e.length;c>h;h++)tr=e[h],M.array(tr,"variant","variant descriptor",e),M.check(2===tr.length,"does not have length 2",tr,"variant descriptor",e),o=M.string(tr[0],"tag","tag",e),r=M.array(tr[1],"fields","variant descriptor",e),i=r.slice(0),i.unshift(["_tag",M.member([o])]),l(o,r,i),s.push(o);return n="initializer for "+t+" (variants "+s.join(", ")+")",a.from_array=function(e){var r;return r="initializer for "+t,M.array(e,"initializer",r),M.check(e.length>=1,"lacks a tag",e,"initializer",r),o=e[0],M.string(o,"tag",r,e),M.member(s)(o),u[o].from_array(e)},a.Type=function(e,r,n,i){return null==n&&(n=""+t+".Type"),M.defined(e,r,n,i),M.defined(e.tag,"tag",n,i),o=e.tag(),M.string(o,"tag","initializer",e),M.member(s)(o),u[o].Type(e,null,"object of type "+t),e},a.coerce=function(t){var e,r;for(r in u)if(e=u[r],t instanceof e)return e.Type(t),t;return a.from_array(t)},a.toString=function(){return"union "+t},a},Le=new RegExp("^-?[1-9][0-9]{0,18}$"),pe="9223372036854775807",de="-9223372036854775808",fe=function(t,e){var r,n,i;return t===e?!1:(n="0"===t.charAt(0),i="0"===e.charAt(0),n&&!i?!0:i&&!n?!1:(r=t.length===e.length?t>e:t.length>e.length,n&&i?r:!r))},xe=function(t){return M.is_string(t)?"0"===t?!0:Le.test(t)?"-"===t.charAt(0)?t.length<de.length||de>=t:t.length<pe.length||pe>=t:!1:!1},Ue=function(t){var e,r,n,i;if(!M.is_simple_map(t))return!1;if(e=Object.keys(t),1!==e.length)return!1;switch(e[0]){case"B":return M.is_string(t.B);case"N":return"nan"===(n=t.N)||"+inf"===n||"-inf"===n;case"I":case"T":return r=null!=(i=t.I)?i:t.T,xe(r);default:return!1}},Ae=function(t){return M.is_bool(t)||M.is_json_number(t)||M.is_string(t)||Ue(t)},Ee=function(t){var e,r,n;if(M.is_array(t)){for(r=0,n=t.length;n>r;r++)if(e=t[r],!Ae(e))return!1;return!0}return!1},Oe=function(t){return Ae(t)||Ee(t)},K=function(t,e,r,n){return null==r&&(r="atomic field value"),M.check(Ae(t),"is not an atomic field value",t,e,r,n),t},Pe=function(t,e,r,n){return null==r&&(r="list value"),M.arrayOf(K)(t,e,r,n),t},ne=function(t,e,r,n){return null==r&&(r="field value"),M.is_array(t)?Pe(t,e,r,n):K(t,e,r,n)},he.FieldOp=O=$e.union_as_list("FieldOp",[["P",[["value",ne]]],["D",[]],["LP",[["at",M.uint],["value",K]]],["LI",[["before",M.uint],["value",K]]],["LD",[["at",M.uint]]],["LM",[["from",M.uint],["to",M.uint]]]]),oe=M.simple_typed_map("datadict",M.field_name,ne),Ye=M.simple_typed_map("update_datadict",M.field_name,O),he.Change=r=$e.union_as_list("Change",[["I",[["tid",M.tid],["rowid",M.rowid],["fields",oe]]],["U",[["tid",M.tid],["rowid",M.rowid],["updates",Ye]]],["D",[["tid",M.tid],["rowid",M.rowid]]]]),U=$e.define("FlobDelta",[["rev",M.uint],["changes",M.arrayOf(r)],["nonce",M.delta_nonce],["metadata",M.delta_metadata]]),s=$e.define("DatastoreListItem",[["dsid",M.string],["path",M.string]]),a=$e.define("DatastoreListResponse",[["token",M.string],["datastores",M.arrayOf(s)]]),c=$e.define("DeltaStreamItem",[["deltas",M.arrayOf(U)],["evicted",M.nullable(M.string)]]),t=$e.define("AwaitResponse",[["delta_stream_data",M.simple_typed_map("delta stream map",M.string,c)],["ds_list",M.nullable(a)]]),l=function(){function t(t){this.obj_manager=e(t)}var e;return e=function(t){var e,r;return r=new A(t),e=new k(r,t)},t.changeFromArray=function(t){return r.from_array(t)},t.prototype.close=function(){return this.obj_manager.destroy()},t.prototype.get_or_create=function(t,e){var r=this;return this.obj_manager.flob_client.get_or_create_db(t,function(t,n,i){return t?e(t):r.obj_manager.open(i,function(t,r){return t?e(t):e(null,i,r)})})},t.prototype.get_by_path=function(t,e){var r=this;return this.obj_manager.flob_client.get_db(t,function(t,n,i){return t?e(t):r.obj_manager.open(i,function(t,r){return t?e(t):e(null,i,r)})})},t.prototype.get=function(t,e){return this.obj_manager.open(t,function(t,r){return t?e(t):e(null,r)})},t}(),e=function(){function t(){this.min_delay_millis=500,this.max_delay_millis=9e4,this.base=1.5,this._failures=0,this.log=!1}return t.prototype.set_log=function(t){this.log=t},t.prototype.set_max_delay_millis=function(t){this.max_delay_millis=t},t.prototype.get_backoff_millis=function(){var t,e;return this._failures+=1,e=Math.min(this.max_delay_millis,this.min_delay_millis*Math.pow(this.base,this._failures-1)),t=(.5+Math.random())*e,this.log&&console.log("get_backoff_millis: failures="+this._failures+", target_delay_millis="+e+", delay_millis="+t),t},t.prototype.reset=function(){return this._failures=0},t}(),j=function(){function t(){this.backoff=new e}var r,n;return n=6e4,r=0,t.prototype.run=function(t,e,r){var i,o,s,a,u,l,h,c=this;return s=null!=(l=e.do_retry)?l:function(){return!0},a=null!=(h=e.giveup_after_ms)?h:n,u=Date.now()+a,o=!1,i=function(){return o?void 0:t(function(){var t,e,n;return t=arguments[0],e=2<=arguments.length?lr.call(arguments,1):[],o?void 0:t&&s(t)?Date.now()>u?(console.error("Giving up due to error",t),r(t)):(n=c.backoff.get_backoff_millis(),console.warn("Retrying in "+n+" ms due to error",t),setTimeout(i,n)):r.apply(null,[t].concat(lr.call(e)))})},i(),function(){return o=!0}},t}(),x=function(){function e(t){this.client=t,this._retry=new j}var r,n;return n=10,r=2419200,e.prototype._run_with_retries=function(t,e,r){var n;return n={giveup_after_ms:1e3*t,do_retry:function(t){var e;return 0===t.status||500<=(e=t.status)&&600>e}},this._retry.run(r,n,e)},e.prototype.delete_db=function(t,e){var r=this;return this._run_with_retries(n,e,function(e){return r.client._deleteDatastoreByPath(t,function(t){return null!=t?e(t):e(null)})})},e.prototype.list_dbs=function(t){var e=this;return this._run_with_retries(r,t,function(t){return e.client._listDatastores(function(e,r){return e?t(e):t(null,r)})})},e.prototype.get_or_create_db=function(t,e){var r=this;return this._run_with_retries(n,e,function(e){return r.client._getOrCreateDatastore(t,function(t,r,n){return r?e(t,r.revision,r.dsid,n):e(t)})})},e.prototype.get_db=function(t,e){var r=this;return this._run_with_retries(n,e,function(e){return r.client._getDatastore(t,function(t,r){return r?e(t,r.revision,r.dsid):e(t)})})},e.prototype.get_deltas=function(t,e,n){var i=this;return this._run_with_retries(r,n,function(r){return i.client._getDeltas(t,e,function(t,n,i){var o,s,a,u;return n?(s=n.deltas(),u=s.length>0?s[s.length-1].rev+1:e,a=function(){var t,e,r;for(r=[],t=0,e=s.length;e>t;t++)o=s[t],r.push(o.json());return r}(),r(t,a,u,i)):r(t)})})},e.prototype.await_deltas=function(t,e){var n=this;return this._run_with_retries(r,e,function(e){return n.client._awaitDeltas(t,function(t,r){var n,i,o,s,a,u;if(r){for(i={},a=0,u=r.length;u>a;a++)s=r[a],o=function(){var t,e,r,i;for(r=s.deltas(),i=[],t=0,e=r.length;e>t;t++)n=r[t],i.push(new U(n.json()));return i}(),i[s.dsid]={deltas:o};return e(t,i)}return e(t)})})},e.prototype.await=function(e,n,i){var o,s=this;return o=this._run_with_retries(r,i,function(r){return s.client._datastoreAwait(e,n,function(e,n){var i,o,s,u,l,h,p,d,f,_;if(e)return r(e);if(d={},u=null,null!=n.deltas){f=n.deltas;for(l in f)i=f[l],s=i.deltas,h=i.evicted,d[l]=new c({evicted:null!=h?h:null,deltas:null!=s?s:[]})}return null!=(null!=(_=n.listdbs)?_.dbs:void 0)&&(u=new a({datastores:function(){var t,e,r,i,s;for(r=n.listdbs.dbs,s=[],t=0,e=r.length;e>t;t++)i=r[t],o=i.dbid,p=i.path,s.push({dsid:o,path:p});return s}(),token:n.listdbs.token})),r(null,new t({delta_stream_data:d,ds_list:u}))})})},e.prototype.put_delta=function(t,e,n){var i,o=this;return i=function(t,e){return n(e)},this._run_with_retries(r,n,function(r){return o.client._putDelta(t,p.Datastore.Delta.parse(e),function(t){return t&&409===t.status?r(null,t):r(t,t)})})},e.prototype.get_snapshot=function(t,e,r){var i=this;return W(null===e,"rev is null"),this._run_with_retries(n,r,function(e){return i.client._getSnapshot(t,function(t,r){var n,i,o,s,a,u,l;if(r){for(n={data:{}},l=r.records(),s=0,a=l.length;a>s;s++)i=l[s],(o=n.data)[u=i.tid]||(o[u]={}),n.data[i.tid][i.rowid]=i.data;return e(t,r.revision,n)}return e(t)})})},e}(),P=function(){function t(t,e,r,n){this.metadata=t,this.changes=e,this.undo_extras=r,this.finalized=null!=n?n:!1}var e;return e=function(t,e){var n,i,o;switch(o=null,i=null,t.tag()){case"I":o="D";break;case"U":o="U",i={};for(Ce in e)tr=e[Ce],i[Ce]="undefined"==typeof tr||null===tr?["D"]:["P",tr];break;case"D":o="I",i=te(e);break;default:throw new Error("Unknown change tag: "+t.tag())}return n=[o,t.tid,t.rowid],null!=i&&n.push(i),r.from_array(n)},t.prototype.add_change=function(t,e){return W(!this.finalized,"add_change: already finalized"),this.changes.push(t),this.undo_extras.push(e)},t.prototype["package"]=function(t,e){return W(this.finalized,"package: not finalized"),new U({metadata:M.string(this.metadata),changes:this.changes.slice(),nonce:t,rev:e})},t.prototype.inverse_changes=function(){var t,r,n,i,o,s;for(n=[],s=this.changes,r=i=0,o=s.length;o>i;r=++i)t=s[r],n.push(e(t,this.undo_extras[r]));return n.reverse(),n},t}(),u=function(){function t(t){this.data=null!=t?t:{}}return t.load_from_flob=function(e){return new t(te(e.data))},t.prototype.apply_change=function(t){switch(t.tag()){case"I":return this._apply_insert(t);case"U":return this._apply_update(t);case"D":return this._apply_delete(t);default:throw new Error("unrecognized tag "+t.tag())}},t.prototype._get_table=function(t){return null==this.data[t]&&(this.data[t]={}),this.data[t]},t.prototype._apply_insert=function(t){var e;return e=this._get_table(t.tid),M.assert(!(t.rowid in e),function(){return"_apply_insert: record already exists: "+JSON.stringify(t)}),e[t.rowid]=te(t.fields),null},t.prototype._apply_update=function(t){var e,r,n,i,o,s,a;r=function(t,e,r){return r[t]=e[t]instanceof Array?e[t].slice():e[t]},e=function(t,e,r){var n,i,o,s,a,u;switch(r.tag()){case"P":return e[t]=te(r.value);case"D":return delete e[t];case"LP":return W(0<=(i=r.at)&&i<e[t].length,"bad index for LP"),e[t][r.at]=te(r.value);case"LI":return null!=e[t]?(W(0<=(o=r.before)&&o<=e[t].length,"bad index for LI"),e[t].splice(r.before,0,te(r.value))):(W(0===r.before,"bad index for LI on nonexistent field"),e[t]=[te(r.value)]);case"LD":return W(0<=(s=r.at)&&s<e[t].length,"bad index for LD"),e[t].splice(r.at,1);case"LM":return W(0<=(a=r.from)&&a<e[t].length,"bad from index for LM"),n=e[t][r.from],e[t].splice(r.from,1),W(0<=(u=r.to)&&u<=e[t].length,"bad to index for LM"),e[t].splice(r.to,0,n);default:throw new Error("field op type "+r.tag()+" is not handled yet")}},s=this._get_table(t.tid),M.assert(t.rowid in s,function(){return"_apply_update: record does not exist: "+JSON.stringify(t)}),o=s[t.rowid],i={},a=t.updates;for(Ce in a)n=a[Ce],r(Ce,o,i),e(Ce,o,n);return i},t.prototype._apply_delete=function(t){var e,r,n,i;n=this._get_table(t.tid),M.assert(t.rowid in n,function(){return"_apply_delete: record does not exist: "+JSON.stringify(t)}),e=te(n[t.rowid]),delete n[t.rowid],i=!0;for(r in n){i=!1;break}return i&&delete this.data[t.tid],e},t.prototype.query=function(t,e){var r,n;return n=this.data[t],null==n?null:(r=n[e],null==r?null:te(r))},t.prototype.list_tables=function(){var t,e;return t=function(){var t;t=[];for(e in this.data)t.push(e);return t}.call(this),t.sort(),t},t.prototype.list_rows_for_table=function(t){var e,r,n;return n=this.data[t],null==n?[]:(e=function(){var e;e=[];for(r in this.data[t])e.push(r);return e}.call(this),e.sort(),e)},t}(),T=function(t){function e(t,r,n,i,o){this.dbid=t,this.resolver=r,this.datastore_model=n,this.sync_state=i,this.flob_client=o,e.__super__.constructor.call(this),this._deleted=!1,this._open=!0,this._commit_queue=new F}return ur(e,t),e.prototype.on=function(t,e){return this.addListener(t,e)},e.prototype.emit=function(t,e,r){if(r)throw new Error("Extra arg: "+JSON.stringify(r));return this.dispatch(t,e)},e.fresh_managed_datastore=function(t,r,n,i,o){var s,a,u;return a=function(){var t,e;for(e=[],s=t=0;10>t;s=++t)e.push(Math.floor(10*Math.random()));return e}().join(""),u=new B(a,null,n,[],[]),new e(i,r,t,u,o)},e.prototype.is_deleted=function(){return this._deleted},e.prototype.mark_deleted=function(){return this._deleted=!0},e.prototype.open=function(){if(this._open)throw new Error("Attempt to open datastore multiple times");return this._open=!0},e.prototype.close=function(){if(!this._open)throw new Error("Attempt to close datastore multiple times");return this._open=!1},e.prototype._do_sync=function(){var t,e,r,n,i,o,s,a,u,l,h,c,p,d,f,_,y,g,m,v,w,b,S;if(0===this.sync_state.server_deltas.length)return{};for(i=this.resolver.resolve(this.sync_state.unsynced_deltas,this.sync_state.server_deltas),n=i.rebased_deltas,t=i.affected_records,o=this.sync_state.unsynced_deltas.slice().reverse(),a=0,c=o.length;c>a;a++)for(r=o[a],v=r.inverse_changes(),u=0,p=v.length;p>u;u++)e=v[u],this.datastore_model.apply_change(e);for(w=this.sync_state.server_deltas,l=0,d=w.length;d>l;l++)for(r=w[l],b=r.changes,h=0,f=b.length;f>h;h++)e=b[h],this.datastore_model.apply_change(e);for(g=0,_=n.length;_>g;g++)for(r=n[g],r.undo_extras=[],S=r.changes,m=0,y=S.length;y>m;m++)e=S[m],s=this.datastore_model.apply_change(e),r.undo_extras.push(s);return this.sync_state.update_unsynced_deltas(n),t},e.prototype._do_commit=function(){var t,e=this;if(!this.sync_state.delta_pending()&&(t=this.sync_state.get_next_commit(),null!=t))return this._commit_queue.request(function(){return e.flob_client.put_delta(e.dbid,t,function(){return e._commit_queue.finish()})})},e.prototype.perform_change=function(t){var e;return e=this.datastore_model.apply_change(t),this.sync_state.add_unsynced_change(t,e),this.emit("sync-state-changed")},e.prototype.sync=function(){var t;return this.sync_state.finalize(),t=this._do_sync(),this._do_commit(),t},e.prototype.get_outgoing_delta_count=function(){return this.sync_state.unsynced_deltas.length},e.prototype.get_incoming_delta_count=function(){return this.sync_state.server_deltas.length
},e.prototype.has_unfinalized_changes=function(){return this.sync_state.has_unfinalized_changes()},e.prototype.receive_server_delta=function(t){return this.sync_state.receive_server_delta(t)?this.emit("sync-state-changed"):this.emit("sync-state-changed")},e.prototype.query=function(t,e){return this.datastore_model.query(t,e)},e.prototype.list_tables=function(){return this.datastore_model.list_tables()},e.prototype.list_rows_for_table=function(t){return this.datastore_model.list_rows_for_table(t)},e}(p.Util.TypedEventSource),B=function(){function t(t,e,r,n,i){this.last_nonce=t,this.pending_delta=e,this.last_rev=r,this.unsynced_deltas=n,this.server_deltas=i}return t.prototype.is_current=function(){return 0===this.unsynced_deltas.length&&0===this.server_deltas.length},t.prototype.add_unsynced_change=function(t,e){var r,n;return r=this.unsynced_deltas.length,0===r||this.unsynced_deltas[r-1].finalized?(n="",this.unsynced_deltas.push(new P(n,[t],[e]))):this.unsynced_deltas[r-1].add_change(t,e)},t.prototype._compact_deltas=function(){var t,e,r,n,i,o,s,a,u,l,h,c,p,d,f;if(n=this.unsynced_deltas.length,!(1>=n)){for(e=[],s=[],i="",r=a=0,p=n-1;p>=0?p>a:a>p;r=p>=0?++a:--a){for(d=this.unsynced_deltas[r].changes,u=0,h=d.length;h>u;u++)t=d[u],e.push(t);for(f=this.unsynced_deltas[r].undo_extras,l=0,c=f.length;c>l;l++)o=f[l],s.push(o);i+=M.string(this.unsynced_deltas[r].metadata)}return this.unsynced_deltas=[new P(i,e,s,!0),this.unsynced_deltas[n-1]]}},t.prototype.get_next_commit=function(){var t,e,r;return W(null==this.pending_delta,"delta pending"),t=this.unsynced_deltas.length,0===t?null:(this._compact_deltas(),e=this.unsynced_deltas[0],e.finalized?(r=this.last_nonce,this.pending_delta=e["package"](r,this.last_rev),this.pending_delta):null)},t.prototype.clear_pending=function(){return this.pending_delta=null},t.prototype.delta_pending=function(){return null!=this.pending_delta},t.prototype.set_metadata=function(t){var e;return e=this.unsynced_deltas.length,W(e>0,"no unsynced deltas"),this.unsynced_deltas[e-1].metadata=M.string(t)},t.prototype.has_unfinalized_changes=function(){var t,e;return e=this.unsynced_deltas.length,0===e?!1:(t=this.unsynced_deltas[e-1],!t.finalized)},t.prototype.finalize=function(){var t;if(this.has_unfinalized_changes())return t=this.unsynced_deltas[this.unsynced_deltas.length-1],W(!t.finalized,"last delta already finalized"),t.finalized=!0},t.prototype.update_unsynced_deltas=function(t){return this.unsynced_deltas=t,this.last_rev+=this.server_deltas.length,this.server_deltas=[]},t.prototype.is_ours=function(t){return this.last_nonce===t.nonce},t.prototype.ack=function(t){return W(this.is_ours(t),"not ours"),W(null!=this.pending_delta,"no pending delta"),W(0===this.server_deltas.length,"server deltas exist"),this.pending_delta=null,this.unsynced_deltas.shift(),this.last_rev++},t.prototype.receive_server_delta=function(t){var e,r;return r=this.server_deltas.length,e=r>0?this.server_deltas[r-1].rev+1:this.last_rev,W(t.rev<=e,"was expecting rev "+e+", but got "+t.rev+" instead!"),t.rev<e?(console.warn("received old delta!"),!1):this.is_ours(t)?(this.ack(t),!1):(this.server_deltas.push(t),this.pending_delta=null,!0)},t}(),he.DatastoreModel=u,R=function(){function t(t){this.update_manager=t,this.cancelled=!1,this.cancel_fn=null}return t.prototype.cancel=function(){return null!=this.cancel_fn&&this.cancel_fn(),this.cancelled=!0},t.prototype.poll=function(){var t,e=this;return t=function(){var r;if(!e.cancelled)return r=JSON.parse(JSON.stringify(e.update_manager._flobid_version_map)),e.cancel_fn=e.update_manager.flob_client.await(r,e.update_manager._last_dslist_token,function(n,i){var o,s,a,u,l,h,c,p,d,f;if(e.cancel_fn=null,n)return 0===n.status?(console.log("await deltas failed (offline):",n),setTimeout(t,1e4)):n.status&&500<=(d=n.status)&&599>=d?(console.warn("server error:",n),setTimeout(t,2e3)):(console.error("Got error in longpoll:",n),setTimeout(t,1e4));f=i.delta_stream_data;for(l in f){for(a=f[l],u=a.deltas,c=0,p=u.length;p>c;c++)s=u[c],e.update_manager._data_queue.push({flobid:l,delta:s});null!=a.evicted?(e.update_manager._data_queue.push({flobid:l,evicted:a.evicted}),delete e.update_manager._flobid_version_map[l]):(h=r[l]+u.length,o=e.update_manager._flobid_version_map[l],null!=o&&(e.update_manager._flobid_version_map[l]=Math.max(o,h)))}return null!=i.ds_list&&(e.update_manager._last_dslist_token=i.ds_list.token,e.update_manager._data_queue.push({dslist:i.ds_list.datastores})),setTimeout(t,0)})},t()},t}(),A=function(){function t(t){this.flob_client=t,this._data_queue=null,this._flobid_version_map={},this._last_dslist_token="[not a token]",this._pending_poll=null,this._running=!1}return t.prototype.run=function(t){return this._data_queue=new i(t),this._running=!0,this._do_longpoll()},t.prototype.stop=function(){return this._pending_poll?this._pending_poll.cancel():void 0},t.prototype.add_poll=function(t,e){var r,n;return W(this._running,"update manager is not running"),r=this._flobid_version_map[t],n=e,null!=r&&(n=Math.max(e,r)),this._flobid_version_map[t]=n,this._do_longpoll()},t.prototype.remove_poll=function(t){return W(this._running,"update manager is not running"),t in this._flobid_version_map?(delete this._flobid_version_map[t],this._do_longpoll()):void 0},t.prototype._do_longpoll=function(){return W(this._running,"update manager is not running"),this._pending_poll&&(this._pending_poll.cancel(),this._pending_poll=null),this._pending_poll=new R(this),this._pending_poll.poll()},t}(),k=function(){function t(t,e){this.update_manager=t,this.flob_client=e,this.update_manager.run(this._handle_server_update.bind(this)),this.cached_objects={},this._dslist_listener=null}return t.prototype.destroy=function(){var t;for(t in this.cached_objects)this.cached_objects[t].close();return this.update_manager.stop()},t.prototype.set_dslist_listener=function(t){return this._dslist_listener=t},t.prototype.evict=function(t){return t in this.cached_objects&&this.cached_objects[t].mark_deleted(),this.update_manager.remove_poll(t)},t.prototype.close=function(t){if(t in this.cached_objects)return this.cached_objects[t].close();throw new Error("Attempt to close unknown datastore: "+t)},t.prototype._handle_server_update=function(t,e){var r,n;return t.dslist?(this._dslist_listener&&this._dslist_listener(t.dslist),e(null)):(n=t.flobid,r=t.delta,null!=t.evicted?(this.evict(n),e(null)):this.retrieve(n,function(t,n){return t?e(t):(n.receive_server_delta(r),e(null))}))},t.prototype.open=function(t,e){return this.cached_objects[t]&&this.cached_objects[t].open(),this.retrieve(t,e)},t.prototype.retrieve=function(t,e){var r,n=this;return r=this.cached_objects[t],null!=r?e(null,r):this.flob_client.get_snapshot(t,null,function(r,i,o){var s,a,l;return r?e(r):(s=u.load_from_flob(o),l=new h,a=T.fresh_managed_datastore(s,l,i,t,n.flob_client),null!=n.cached_objects[t]?e(null,n.cached_objects[t]):(n.update_manager.add_poll(t,a.sync_state.last_rev),n.cached_objects[t]=a,e(null,a)))})},t}(),he.FieldOpTransformer=E=function(){function t(t){var i,o,s,a,l,h,c,p,d,g=this;for(this.rule_name=null!=t?t:"default",this.precedence=n[this.rule_name],this._transforms={},s=0,h=r.length;h>s;s++)o=r[s],this._transforms[o]={};for(d=["P","D"],a=0,c=d.length;c>a;a++)for(o=d[a],l=0,p=e.length;p>l;l++)i=e[l],this._transforms[o][i]=f,this._transforms[i][o]=_;this._transforms.P.P=function(t,e){var r;return r=g.precedence(t.value,e.value),"left"===r?[t,null]:[null,e]},this._transforms.P.D=function(t,e){var r;return r=g.precedence(t.value,null),"left"===r?[t,null]:[null,e]},this._transforms.D.P=function(t,e){var r;return r=g.precedence(null,e.value),"left"===r?[t,null]:[null,e]},this._transforms.D.D=function(t,e){var r;return r=g.precedence(null,null),"left"===r?[t,null]:[null,e]},this._transforms.LP.LP=function(t,e){var r;return t.at!==e.at?[t,e]:(r=g.precedence(t.value,e.value),"left"===r?[t,null]:[null,e])},this._transforms.LP.LI=function(t,e){var r;return r=u(t),r.at+=e.before<=t.at?1:0,[r,e]},this._transforms.LP.LD=function(t,e){var r;return t.at===e.at?[null,e]:(r=u(t),r.at-=e.at<t.at?1:0,[r,e])},this._transforms.LP.LM=function(t,e){var r;return r=u(t),t.at===e.from?r.at=e.to:(r.at-=e.from<r.at?1:0,r.at+=e.to<=r.at?1:0),[r,e]},this._transforms.LI.LP=y(this._transforms.LP.LI),this._transforms.LI.LI=function(t,e){var r,n,i;return i=[u(t),u(e)],r=i[0],n=i[1],t.before<e.before?n.before+=1:r.before+=1,[r,n]},this._transforms.LI.LD=function(t,e){var r,n,i;return i=[u(t),u(e)],r=i[0],n=i[1],r.before-=e.at<t.before?1:0,n.at+=t.before<=e.at?1:0,[r,n]},this._transforms.LI.LM=function(t,e){var r,n,i,o;return o=[u(t),u(e)],n=o[0],i=o[1],t.before===e.to+1&&e.from<=e.to?[t,e]:t.before===e.to&&e.from>e.to?(n.before++,i.from++,[n,i]):(r=e.from<t.before?t.before-1:t.before,i.from+=t.before<=e.from?1:0,n.before=e.to<r?r+1:r,i.to+=r<=e.to?1:0,[n,i])},this._transforms.LD.LP=y(this._transforms.LP.LD),this._transforms.LD.LI=y(this._transforms.LI.LD),this._transforms.LD.LD=function(t,e){var r,n,i;return t.at===e.at?[null,null]:(i=[u(t),u(e)],r=i[0],n=i[1],t.at<e.at?n.at-=1:r.at-=1,[r,n])},this._transforms.LD.LM=function(t,e){var r,n,i;return t.at===e.from?(r=u(t),r.at=e.to,[r,null]):(i=[u(t),u(e)],r=i[0],n=i[1],r.at-=e.from<r.at?1:0,r.at+=e.to<=r.at?1:0,n.to+=n.from<n.to?1:0,n.from-=t.at<n.from?1:0,n.to-=t.at<n.to?1:0,n.to-=n.from<n.to?1:0,[r,n])},this._transforms.LM.LP=y(this._transforms.LP.LM),this._transforms.LM.LI=function(t,e){var r,n,i,o;return o=[u(t),u(e)],n=o[0],i=o[1],e.before===t.to+1&&t.from<=t.to?[t,e]:e.before===t.to&&t.from>t.to?(n.from++,n.to++,[n,i]):(r=t.from<e.before?e.before-1:e.before,n.from+=e.before<=t.from?1:0,i.before=t.to<r?r+1:r,n.to+=r<=t.to?1:0,[n,i])},this._transforms.LM.LD=y(this._transforms.LD.LM),this._transforms.LM.LM=function(t,e){var r,n,i,o,s,a,l,h,c,p,d;return t.from===e.from?t.to===e.to?[null,null]:e.from===e.to?[t,e]:(o=u(e),o.from=t.to,[null,o]):t.to===t.from?(i=u(t),i.from+=(e.to<=t.from)-(e.from<t.from),t.from===e.to&&e.from<e.to&&i.from--,i.to=i.from,[i,e]):e.to===e.from?(o=u(e),o.from+=(t.to<=e.from)-(t.from<e.from),o.to=o.from,[t,o]):(l=[u(t),u(e)],i=l[0],o=l[1],t.to===e.to&&t.from>t.to&&e.from>e.to?(i.to++,e.from>t.from?i.from++:o.from++,[i,o]):t.from===e.to&&e.from===t.to&&t.from<t.to?(o.from--,i.from++,[i,o]):t.from>t.to&&e.from<e.to&&e.to+1===t.to?[t,e]:(h=[t.to,t.from],s=h[0],r=h[1],s+=t.from<s?1:0,s-=e.from<s?1:0,s+=e.to<s?1:0,r-=e.from<r?1:0,r+=e.to<=r?1:0,s-=s>r?1:0,c=[e.to,e.from],a=c[0],n=c[1],a+=e.from<a?1:0,a-=t.from<a?1:0,a+=t.to<=a?1:0,n-=t.from<n?1:0,n+=t.to<=n?1:0,a-=a>n?1:0,p=[s,r],i.to=p[0],i.from=p[1],d=[a,n],o.to=d[0],o.from=d[1],[i,o]))}}var e,r,n,i,o,s,a,u,l,h,c,p,d,f,_,y,g,m,v;for(y=function(t){return W(null!=t),function(e,r){var n,i,o;return o=t(r,e),n=o[0],i=o[1],[i,n]}},i=["null","bool","num","str","blob","ts","list"],o={},h=m=0,v=i.length;v>m;h=++m)g=i[h],o[g]=h;return l=function(t){if(null==t)return"null";if(M.is_bool(t))return"bool";if(null!=t.I||M.is_number(t))return"num";if(M.is_string(t))return"str";if(null!=t.B)return"blob";if(t instanceof Date)return"ts";if(M.is_array(t))return"list";throw new Error("Unrecognized value "+t)},d=function(t){return M.is_number(t)||null!=t.I},s=function(t){return null!=t.I?parseInt(t.I):t},p=function(t,e){var r,n,i;for(r=n=0,i=t.length;i>=0?i>n:n>i;r=i>=0?++n:--n){if(r>=e.length)return!1;if(c(t[r],e[r]))return!0;if(c(e[r],t[r]))return!1}return e.length>t.length},t._is_less_than=c=function(t,e){var r,n;if(r=l(t),n=l(e),r!==n)return o[r]<o[n];if("null"===r)return!1;if("bool"===r)return e&&!t;if("num"===r)return null!=t.I&&null!=e.I?fe(t.I,e.I):s(t)<s(e);if("str"===r)return e>t;if("blob"===r)return t.B<e;if("ts"===r)return e>t;if("list"===r)return p(t,e);throw new Error("unknown type "+r)},t._compute_sum=a=function(t,e,r){var n,i,o,s,a,u;return n=null!=t.I&&null!=e.I&&null!=r.I,null!=t.I&&(t=parseInt(t.I)),null!=e.I&&(e=parseInt(e.I)),null!=r.I&&(r=parseInt(r.I)),s=0x8000000000000000,a=0x10000000000000000,u=0xfffffffffffff800,i=e-t,o=r+i,n&&(o>=s&&(o-=u),-s>o&&(o+=u),o={I:""+o}),o},_=function(t,e){return[null,e]},f=function(t){return[t,null]},r=["P","D","LP","LI","LD","LM"],e=["LP","LI","LD","LM"],t.copy=u=function(t){return O.from_array(JSON.parse(JSON.stringify(t)))},n={"default":function(){return"right"},remote:function(){return"right"},local:function(){return"left"},min:function(t,e){return c(t,e)?"left":"right"},max:function(t,e){return c(t,e)?"right":"left"},sum:function(){return"right"}},t.prototype.transform=function(t,e,r){var n,i,o,s,u;return null==r&&(r=null),"sum"===this.rule_name&&"P"===t.tag()&&"P"===e.tag()&&(null==r&&(r={I:"0"}),d(r)&&d(t.value)&&d(e.value))?(o=a(r,t.value,e.value),n=i=O.from_array(["P",o]),[n,i,e.value]):(s=this._transforms[t.tag()][e.tag()](t,e),u=function(){switch(e.tag()){case"P":return e.value;case"D":return null;default:return{L:!0}}}(),s.push(u),s)},t}(),he.ChangeTransformer=n=function(){function t(){this._transform_rules={},this._default_transformer=new E}var e,n,i,o,s,a,u,l;for(e={},l=["default","local","remote","min","max","sum"],a=0,u=l.length;u>a;a++)i=l[a],e[i]=new E(i);return s=function(t){return W(null!=t),function(e,r){var n,i,o;return o=t(r,e),n=o[0],i=o[1],[i,n]}},n=function(t){return t instanceof Array?t.slice():t},o=function(t,e){return t.tid===e.tid&&t.rowid===e.rowid},t.is_no_op=function(t){var e,r;if("U"!==t.tag())return!1;r=t.updates;for(Ce in r)return e=r[Ce],!1;return!0},t.compact=function(t){var e,r,n,i;for(e=[],n=0,i=t.length;i>n;n++)r=t[n],this.is_no_op(r)||e.push(r);return e},t.prototype.set_field_transformer=function(t,r,n){var i;return null==(i=this._transform_rules)[t]&&(i[t]={}),this._transform_rules[t][r]=e[n]},t.prototype.get_field_transformer=function(t,r){var n;return t in this._transform_rules?null!=(n=this._transform_rules[t][r])?n:this._default_transformer:e["default"]},t.prototype.transform_ii=function(t,e){var i,s,a;return o(t,e)?(i=function(t){var e,i,o;i={},o=t.fields;for(Ce in o)tr=o[Ce],i[Ce]=O.from_array(["P",n(tr)]);return e=r.from_array(["U",t.tid,t.rowid,i]),e.undo_extra={},e},s=i(t),a=i(e),this.transform_uu(s,a)):[[t],[e]]},t.prototype.transform_iu=function(t,e){return o(t,e)?W(!1,"Couldn't have updated a row that hasn't been inserted yet!"):[[t],[e]]},t.prototype.transform_id=function(t,e){return o(t,e)?W(!1,"Couldn't have deleted a row that hasn't been inserted yet!"):[[t],[e]]},t.prototype.transform_ui=s(t.prototype.transform_iu),t.prototype.transform_uu=function(t,e){var n,i,s,a,u,l,h,c,p,d,f,_,y,g,m,v,w,b;if(!o(t,e))return[[t],[e]];y=[{},{}],c=y[0],p=y[1],h={},g=t.updates;for(Ce in g)n=g[Ce],Ce in e.updates?(i=e.updates[Ce],d=null!=(v=t.undo_extra[Ce])?v:null,f=this.get_field_transformer(t.tid,Ce),w=f.transform(n,i,d),s=w[0],a=w[1],_=w[2],null!=s&&(c[Ce]=s,h[Ce]=null!=_?_:null),null!=a&&(p[Ce]=a)):(c[Ce]=n,h[Ce]=null!=(m=t.undo_extra[Ce])?m:null);b=e.updates;for(Ce in b)i=b[Ce],Ce in t.updates||(p[Ce]=i);return u=r.from_array(["U",t.tid,t.rowid,c]),u.undo_extra=h,l=r.from_array(["U",e.tid,e.rowid,p]),[[u],[l]]},t.prototype.transform_ud=function(t,e){return o(t,e)?[[],[e]]:[[t],[e]]},t.prototype.transform_di=s(t.prototype.transform_id),t.prototype.transform_du=s(t.prototype.transform_ud),t.prototype.transform_dd=function(t,e){return o(t,e)?[[],[]]:[[t],[e]]},t}(),he.DefaultResolver=h=function(){function t(){this._change_transformer=new n}return t.prototype.add_resolution_rule=function(t,e,r){return this._change_transformer.set_field_transformer(t,e,r)},t.prototype._transform_one=function(t,e){var r,i,o,s,a;return r=function(t){switch(t.tag()){case"I":return"i";case"U":return"u";case"D":return"d";default:throw new Error("unrecognized op type "+t.tag())}},s="transform_"+r(t)+r(e),a=this._change_transformer[s](t,e),i=a[0],o=a[1],i=n.compact(i),o=n.compact(o),[i,o]},t.prototype._transform_list=function(t,e){var r,n,i,o,s,a,u,l,h,c,p,d,f,_;if(0===t.length)return[[],e];if(0===e.length)return[t,[]];for(r=t[0],n=e[0],d=this._transform_one(r,n),o=d[0],s=d[1],f=this._transform_list(t.slice(1),s),i=f[0],s=f[1],l=0,c=i.length;c>l;l++)a=i[l],o.push(a);for(_=this._transform_list(o,e.slice(1)),o=_[0],u=_[1],h=0,p=u.length;p>h;h++)a=u[h],s.push(a);return[o,s]},t.prototype._resolve=function(t,e){var r,n,i,o,s,a,u;for(o=e.slice(),n=[],s=0,a=t.length;a>s;s++)i=t[s],u=this._transform_list(i,o),r=u[0],o=u[1],n.push(r);return[n,o]},t.prototype.resolve=function(t,e){var n,i,o,s,a,u,l,h,c,p,d,f,_,y,g,m,v,w,b,S,D,A,O,E,x,U,C,T,k,R,I,L,j;for(d=[],v=0,D=t.length;D>v;v++){for(h=t[v],i=[],I=h.changes,p=w=0,A=I.length;A>w;p=++w)s=I[p],u=r.from_array(JSON.parse(JSON.stringify(s))),u.undo_extra=te(h.undo_extras[p]),i.push(u);d.push(i)}for(g=[],b=0,O=e.length;O>b;b++)for(h=e[b],L=h.changes,S=0,E=L.length;E>S;S++)o=L[S],g.push(o);for(j=this._resolve(d,g),_=j[0],l=j[1],y=[],p=T=0,x=_.length;x>T;p=++T){for(a=_[p],m=null,f="",c=t[p].finalized,k=0,U=a.length;U>k;k++)s=a[k],delete s.undo_extra;a.length>0&&y.push(new P(f,a,m,c))}for(n={},R=0,C=l.length;C>R;R++)o=l[R],o.tid in n||(n[o.tid]={}),n[o.tid][o.rowid]=!0;return{rebased_deltas:y,affected_records:n}},t}(),F=function(){function t(){this._waiting=[],this._running=!1}return t.prototype._run_next=function(){var t;this._running||this._waiting.length>0&&(t=this._waiting[0],this._waiting.shift(),this._running=!0,t())},t.prototype.request=function(t){return this._waiting.push(t),this._run_next()},t.prototype.finish=function(){return this._running=!1,setTimeout(this._run_next.bind(this),0)},t}(),i=function(){function t(t){this.consumer=t,this.items=[],this.sync_queue=new F}return t.prototype.consume=function(){var t=this;return this.sync_queue.request(function(){var e;return 0===t.items.length?t.sync_queue.finish():(e=t.items.shift(),t.consumer(e,function(e){if(e)throw e;return t.sync_queue.finish(),t.consume()}))})},t.prototype.push=function(t){return this.items.push(t),this.consume()},t.prototype.run=function(){return this.consume()},t}(),p.Datastore.DatastoreListChanged=function(){function t(t){this._dsids=t}return t.prototype.toString=function(){return"Dropbox.Datastore.DatastoreListChanged("+this._dsids.length+" datastores)"},t.prototype.listDatastoreIds=function(){return this._dsids},t}(),p.Datastore.impl.EventSourceWithInitialData=function(t){function e(t){this.options=t,e.__super__.constructor.call(this,t),this._have_event=!1,this._last_event=null,this._listenersChanged=new p.Util.EventSource}return ur(e,t),e.prototype._clearLastEvent=function(){return this._have_event=!1,this._last_event=null},e.prototype.addListener=function(t){var r;return r=e.__super__.addListener.call(this,t),this._have_event&&t(event),this._listenersChanged.dispatch(this._listeners),r},e.prototype.removeListener=function(t){var r;return r=e.__super__.removeListener.call(this,t),this._listenersChanged.dispatch(this._listeners),r},e.prototype.dispatch=function(t){return this._last_event=t,this._have_event=!0,e.__super__.dispatch.call(this,t)},e}(p.Util.EventSource),p.Datastore.DatastoreManager=function(){function t(t){var e=this;if(!t.isAuthenticated())throw new Error("DatastoreManager requires an authenticated Dropbox.Client!");this._flob_client=new x(t),this._datasync=new l(this._flob_client),this._dslist_initialized=!1,this.datastoreListChanged=new p.Datastore.impl.EventSourceWithInitialData,this.datastoreListChanged._listenersChanged.addListener(function(t){return 0!==t.length?e._init_live_dslist():void 0})}var e;return e="default",t.prototype.datastoreListChanged=null,t.prototype.close=function(){return this._datasync.close()},t.prototype.toString=function(){return"Dropbox.Datastore.DatastoreManager()"},t.prototype._getDatastoreIdsFromListResponse=function(t){var e;return function(){var r,n,i;for(i=[],r=0,n=t.length;n>r;r++)e=t[r],i.push(e.path);return i}()},t.prototype._init_live_dslist=function(){var t,e=this;if(!this._dslist_initialized)return this._dslist_initialized=!0,t=function(t){return e.datastoreListChanged.dispatch(new p.Datastore.DatastoreListChanged(e._getDatastoreIdsFromListResponse(t)))},this._datasync.obj_manager.set_dslist_listener(t),this._flob_client.list_dbs(function(e,r){return e?(console.warn("Failed to get datastore list"),void 0):t(r)})},t.prototype._getDatastorePathById=function(t,e){return this.listDatastores(function(r,n){var i,o,s;if(r)return e(r);for(o=0,s=n.length;s>o;o++)if(i=n[o],i.dsid===t)return e(null,i.path);return e(null,null)})},t.prototype._getOrCreateDatastoreByPath=function(t,e){var r=this;return this._datasync.get_or_create(t,function(n,i,o){return n?e(n):e(null,new p.Datastore(r,o,i,t))}),void 0},t.prototype._getExistingDatastoreByPath=function(t,e){var r=this;return this._datasync.get_by_path(t,function(n,i,o){return n?e(n):e(null,new p.Datastore(r,o,i,t))}),void 0},t.prototype.openDefaultDatastore=function(t){return this._getOrCreateDatastoreByPath(e,t)},t.prototype.openDatastore=function(t,e){return this._getExistingDatastoreByPath(t,e),void 0},t.prototype.createDatastore=function(t){var e,r,n;for(r="",e=n=0;20>n;e=++n)r+=Math.floor(10*Math.random());return r="_"+r,this._getOrCreateDatastoreByPath(r,t),void 0},t.prototype.deleteDatastore=function(t,e){return this._flob_client.delete_db(t,function(t){return t&&e(t),e(null)}),void 0},t.prototype.listDatastoreIds=function(t){var e=this;return this.datastoreListChanged._have_event?t(null,this.datastoreListChanged._last_event.listDatastoreIds()):(this._flob_client.list_dbs(function(r,n){return r?t(r):t(null,e._getDatastoreIdsFromListResponse(n))}),void 0)},t}(),p.Datastore.Delta=function(){function t(t){this.revision=t.rev,this.metadata=t.metadata,this.nonce=t.nonce||null,this.changes=t.changes,this._json=null}return t.parse=function(t){return t&&"object"==typeof t?new p.Datastore.Delta(t):t},t.prototype.metadata=null,t.prototype.revision=null,t.prototype.nonce=null,t.prototype.changes=null,t.changes,t.prototype.json=function(){return this._json||(this._json={rev:this.revision,metadata:this.metadata,nonce:this.nonce,changes:this.changes})},t}(),p.Datastore.DeltaSequence=function(){function t(t,e){var r;this.dsid=e,this._deltas=function(){var e,n,i,o;for(i=t.deltas,o=[],e=0,n=i.length;n>e;e++)r=i[e],o.push(p.Datastore.Delta.parse(r));return o}(),this._json=null}return t.parse=function(t,e){return t&&"object"==typeof t?new p.Datastore.DeltaSequence(t,e):t},t.prototype.dsid=null,t.prototype.deltas=function(){return this._deltas},t}(),p.Datastore.List=function(){function t(t,e,r){this._datastore=t,this._record=e,this._field=r}return t.prototype.toString=function(){return"Datastore.List(("+this._record._tid+", "+this._record._rid+", "+this._field+"): "+JSON.stringify(this._array)+")"},t.prototype._array=function(){return this._record._rawFieldValues()[this._field]},t.prototype._checkValid=function(){if(this._record._checkNotDeleted(),!M.is_array(this._array()))throw new Error("Attempt to operate on deleted list ("+this._record._tid+", "+this._record._rid+", "+this._field+")")},t.prototype._storeUpdate=function(t){var e;return e={},e[this._field]=t,this._record._storeUpdate(e),void 0},t.prototype._fixInsertionIndex=function(t){var e,r;if(!we(t))throw new RangeError("Index not a number: "+t);if(e=this._array().length,r=t>=0?t:e+t,r>=0&&e>=r)return r;throw new RangeError("Bad index for list of length "+e+": "+t)},t.prototype._fixIndex=function(t){var e,r;if(r=this._fixInsertionIndex(t),e=this._array().length,e>r)return r;throw new RangeError("Bad index for list of length "+e+": "+t)},t.prototype.get=function(t){var e;return this._checkValid(),e=te(this._array()[this._fixIndex(t)]),ae(void 0,void 0,void 0,e)},t.prototype.set=function(t,e){return this._checkValid(),t=this._fixIndex(t),this._storeUpdate(["LP",t,Ze(e,!1)]),void 0},t.prototype.length=function(){return this._checkValid(),this._array().length},t.prototype.pop=function(){if(this._checkValid(),0===this._array().length)throw new Error("List is empty");return this.remove(this._array.length-1)},t.prototype.push=function(t){return this._checkValid(),this.insert(this._array().length,t),void 0},t.prototype.shift=function(){if(this._checkValid(),0===this._array().length)throw new Error("List is empty");return this.remove(0)},t.prototype.unshift=function(t){return this.insert(0,t),void 0},t.prototype.splice=function(){var t,e,r,n,i,o,s,a,u;if(n=arguments[0],e=arguments[1],t=3<=arguments.length?lr.call(arguments,2):[],this._checkValid(),!we(e)||0>e)throw new RangeError("Bad second arg to splice: "+n+", "+e);for(n=this._fixInsertionIndex(n),i=this.slice(n,n+e),r=s=0;e>=0?e>s:s>e;r=e>=0?++s:--s)this.remove(n);for(a=0,u=t.length;u>a;a++)o=t[a],this.insert(n,o),n++;return i},t.prototype.move=function(t,e){return this._checkValid(),t=this._fixIndex(t),e=this._fixIndex(e),t===e?void 0:(this._storeUpdate(["LM",t,e]),void 0)},t.prototype.remove=function(t){return this._checkValid(),t=this._fixIndex(t),this._storeUpdate(["LD",t]),rr},t.prototype.insert=function(t,e){return this._checkValid(),t=this._fixInsertionIndex(t),this._storeUpdate(["LI",t,Ze(e,!1)]),void 0},t.prototype.slice=function(t,e){var r;return this._checkValid(),function(){var n,i,o,s;for(o=this._array().slice(t,e),s=[],n=0,i=o.length;i>n;n++)r=o[n],s.push(ae(void 0,void 0,void 0,r));return s}.call(this)},t.prototype.toArray=function(){var t;return this._checkValid(),function(){var e,r,n,i;for(n=this._array().slice(),i=[],e=0,r=n.length;r>e;e++)t=n[e],i.push(ae(void 0,void 0,void 0,t));return i}.call(this)},t}(),p.Datastore.Record=function(){function t(t,e,r){this._datastore=t,this._tid=e,this._rid=r,this._deleted=!1,this._record_cache=this._datastore._record_cache,this._managed_datastore=this._datastore._managed_datastore}return t.prototype.get=function(t){var e;return this._checkNotDeleted(),e=this._rawFieldValues(),t in e?ae(this._datastore,this,t,e[t]):null},t.prototype.set=function(t,e){var r;return r={},r[t]=e,this.update(r)},t.prototype.getFields=function(){var t,e,r,n;this._checkNotDeleted(),t={},n=this._rawFieldValues();for(e in n)r=n[e],t[e]=ae(this._datastore,this,e,r);return t},t.prototype.update=function(t){var e,r,n;this._checkNotDeleted(),e={};for(r in t)n=t[r],e[r]=null!=n?["P",Ze(n)]:["D"];return this._storeUpdate(e),this},t.prototype.deleteRecord=function(){var t;return this._checkNotDeleted(),this._deleted=!0,this._record_cache.remove(this._tid,this._rid),t=l.changeFromArray(["D",this._tid,this._rid]),this._managed_datastore.perform_change(t),this._datastore._recordsChangedLocally([this]),this},t.prototype.hasField=function(t){var e;return e=this._rawFieldValues(),t in e},t.prototype.getId=function(){return this._rid},t.prototype.getTable=function(){return this._datastore.getTable(this._tid)},t.prototype.isDeleted=function(){return this._deleted},t.prototype.toString=function(){var t;return t=this.isDeleted()?"deleted":JSON.stringify(this.getFields()),"Dropbox.Datastore.Record(("+this._tid+", "+this._rid+"): "+t+")"},t.prototype._rawFieldValues=function(){return this._managed_datastore.query(this._tid,this._rid)},t.prototype._storeUpdate=function(t){var e;e=l.changeFromArray(["U",this._tid,this._rid,t]),this._managed_datastore.perform_change(e),this._datastore._recordsChangedLocally([this])},t.isValidId=function(t){var e;return e=new RegExp("^[-._+/=0-9a-zA-Z]{1,32}$"),Se(t)&&e.test(t)},t.prototype._checkNotDeleted=function(){if(this._deleted)throw new Error("Attempt to operate on deleted record ("+this._tid+", "+this._rid+")")},t}(),p.Datastore.RecordsChanged=function(){function t(t,e){this._recordsByTable=t,this._local=e}return t.prototype.toString=function(){var t,e,r,n,i,o,s;i=0,r=0,s=this._recordsByTable;for(o in s)t=s[o],i+=1,r+=t.length;return n=""+i+" "+(1===i?"table":"tables"),e=""+r+" "+(1===r?"record":"records"),"Dropbox.Datastore.RecordsChanged("+e+" in "+n+" changed "+(this._local?"locally":"remotely")+")"},t._fromRecordList=function(e,r){var n,i,o,s,a;for(i={},s=0,a=e.length;a>s;s++)n=e[s],o=n._tid,null==i[o]&&(i[o]=[]),i[o].push(n);return new t(i,r)},t.prototype.affectedRecordsByTable=function(){return this._recordsByTable},t.prototype.affectedRecordsForTable=function(t){var e;return null!=(e=this._recordsByTable[t])?e:[]},t.prototype.isLocal=function(){return this._local},t}(),L=p.Datastore.RecordsChanged,p.Datastore.Snapshot=function(){function t(t,e){this.dsid=e,this.revision=t.rev,this._records=t.rows,this._json=null}return t.parse=function(t,e){return t&&"object"==typeof t?new p.Datastore.Snapshot(t,e):t},t.prototype.dsid=null,t.prototype.revision=null,t.prototype.records=function(){return this._records},t.prototype.json=function(){return this._json||(this._json={dsid:this.dsid,rev:this.revision,rows:this._records})},t}(),p.Datastore.Stat=function(){function t(t,e){this.path=t.path||e||null,this.dsid=t.dbid.toString(),this.revision="rev"in t?t.rev:null,this._json=null}return t.parse=function(t,e){return t&&"object"==typeof t?new p.Datastore.Stat(t,e):t},t.prototype.path=null,t.prototype.dsid=null,t.prototype.revision=null,t.prototype.json=function(){return this._json||(this._json={path:this.path,dbid:this.dsid,rev:this.revision})},t}(),p.Datastore.SyncSet=function(){function t(){this._cursors={}}return t.prototype.cursors=function(){return this._cursors},t.prototype.set=function(t,e){var r;return"object"==typeof t?(r=t.dsid,e=t.revision):r=t,this._cursors[r]=e,this},t.prototype.remove=function(t){var e;return e="object"==typeof t?t.dsid:t,delete this._cursors[e],this},t}(),p.Datastore.Table=function(){function t(t,e){this._datastore=t,this._tid=e,this._record_cache=this._datastore._record_cache,this._managed_datastore=this._datastore._managed_datastore}return t.prototype.getId=function(){return this._tid},t.prototype.get=function(t){var e,r;if(!p.Datastore.Record.isValidId(t))throw new Error("Invalid record ID: "+t);return r=this._record_cache.get(this._tid,t),null!=r?(W(!r._deleted),r):(e=this._managed_datastore.query(this._tid,t),null==e?null:this._record_cache.getOrCreate(this._tid,t))},t.prototype.getOrInsert=function(t,e){var r;return r=this.get(t),r?r:this._insertWithId(t,e)},t.prototype.insert=function(t){var e;return e=this._datastore._generateRid(),W(null==this.get(e)),this._insertWithId(e,t)},t.prototype.query=function(t){var e,r,n,i,o,s,a;for(o=this._managed_datastore.list_rows_for_table(this._tid),n=[],s=0,a=o.length;a>s;s++)i=o[s],e=this._managed_datastore.query(this._tid,i),(null==t||Te(t,e))&&(r=this.get(i),W(null!=r),n.push(r));return n},t.prototype.setResolutionRule=function(t,e){if("remote"!==e&&"local"!==e&&"min"!==e&&"max"!==e&&"sum"!==e)throw new Error(""+e+" is not a valid resolution rule. Valid rules are 'remote', 'local', 'min', 'max', and 'sum'.");return this._managed_datastore.resolver.add_resolution_rule(this._tid,t,rule_name),this},t.isValidId=function(t){var e;return e=new RegExp("^[-._+/=0-9a-zA-Z]{1,32}$"),Se(t)&&e.test(t)},t.prototype.toString=function(){return"Dropbox.Datastore.Table("+this._tid+")"},t.prototype._insertWithId=function(t,e){var r,n,i;n={};for(Ce in e)tr=e[Ce],n[Ce]=Ze(tr);return r=l.changeFromArray(["I",this._tid,t,n]),this._managed_datastore.perform_change(r),i=this._record_cache.getOrCreate(this._tid,t),this._datastore._recordsChangedLocally([i]),i},t}(),ee=function(t){var e,r,n;for(n=[],e=0,r=t.length;r>e;e++)tr=t[e],n.push(te(tr));return n},re=function(t){var e;e={};for(Ce in t)tr=t[Ce],e[Ce]=te(tr);return e},he.clone=te=function(t){return t instanceof Array?ee(t):"object"==typeof t?re(t):t},z="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_",Be=function(t){return t[Math.floor(Math.random()*t.length)]},Me=function(t){var e;return function(){var r,n;for(n=[],e=r=0;t>=0?t>r:r>t;e=t>=0?++r:--r)n.push(Be(z));return n}().join("")},ye=function(t){return t===!0||t===!1||t&&"object"==typeof t&&t.constructor===Boolean},be=function(t){return"number"==typeof t||t&&"object"==typeof t&&t.constructor===Number},we=function(t){return be(t)&&!isNaN(t)&&isFinite(t)},Se=function(t){return"string"==typeof t||t&&"object"==typeof t&&t.constructor===String},_e=function(t){return"[object Array]"===Object.prototype.toString.call(t)
},De=function(t){return"[object Uint8Array]"===Object.prototype.toString.call(t)},ge=function(t){return"[object Date]"===Object.prototype.toString.call(t)},me=function(t){for(Ce in t)return!1;return!0},he.uint8ArrayFromBase64String=Qe=function(t){var e,r,n,i,o;for(t=t.replace("-","+").replace("_","/"),e=V(t),n=e.length,i=new Uint8Array(n),r=o=0;n>=0?n>o:o>n;r=n>=0?++o:--o)i[r]=e.charCodeAt(r);return i},he.base64StringFromUint8Array=$=function(t){var e,r,n,i,o;for(r="",i=0,o=t.length;o>i;i++)e=t[i],r+=String.fromCharCode(e);return n=Q(r),n.replace("+","-").replace("/","_").replace(/[\=]+$/g,"")},C="dbxInt64",ve=function(t){var e;return t&&"object"==typeof t&&t.constructor===Number&&isFinite(t)?(e=t[C],!Se(e)||"0"!==e&&!Le.test(e)?!1:!0):!1},er=function(t){var e,r;if(!t&&"object"==typeof t&&t.constructor===Number&&isFinite(t))throw new Error("Not a finite boxed number: "+t);if(r=t[C],!Se(r)||"0"!==r&&!Le.test(r))throw new Error("Missing or invalid tag in int64: "+r);if(e=parseInt(r,10),e!==Number(t))throw new Error("Tag in int64 does not match value "+Number(t)+": "+r);return t},he.toDsValue=Ze=function(t,e){var r,n;if(null==e&&(e=!0),null===t||"undefined"==typeof t)throw new Error("Bad value: "+t);if(Se(t))return t;if(ye(t))return t;if(be(t)){if(null!=t[C])return er(t),{I:t[C]};if(isFinite(t))return t;if(isNaN(t))return{N:"nan"};if(1/0===Number(t))return{N:"+inf"};if(Number(t)===-1/0)return{N:"-inf"};throw new Error("Unexpected number: "+t)}if(_e(t)){if(e)return function(){var e,r,i;for(i=[],e=0,r=t.length;r>e;e++)n=t[e],i.push(Ze(n,!1));return i}();throw new Error("Nested array not allowed: "+JSON.stringify(t))}if(ge(t))return r=Math.round(t.getTime()),{T:""+r};if(De(t))return{B:$(t)};throw new Error("Unexpected object: "+JSON.stringify(t))},he.fromDsValue=ae=function(t,e,r,n){if(Se(n))return n;if(ye(n))return n;if(be(n))return n;if(_e(n))return new p.Datastore.List(t,e,r);if("object"!=typeof n)throw new Error("Unexpected value: "+n);if(n.I)return ce(n.I);if(!n.N){if(n.B)return Qe(n.B);if(n.T)return new Date(parseInt(n.T,10));throw new Error("Unexpected object: "+JSON.stringify(n))}switch(n.N){case"nan":return 0/0;case"+inf":return 1/0;case"-inf":return-1/0;default:throw new Error("Unexpected object: "+JSON.stringify(n))}},he.matchDsValues=Te=function(t,e){var r,n,i;n=function(t,e){if(null==t)throw new Error("Unexpected object: "+t);return null==e?!1:r(t,e)},r=function(t,e){var r,i,o,s,a,u;if(Ze(t),Se(t)&&Se(e))return String(t)===String(e);if(ye(t)&&ye(e))return"object"==typeof t&&(t=t.valueOf()),"object"==typeof e&&(e=e.valueOf()),Boolean(t)===Boolean(e);if(be(t)&&(be(e)||null!=e.N||null!=e.I))return e=ae(void 0,void 0,void 0,e),t[C]&&e[C]?(s=[ce(t),ce(e)],t=s[0],e=s[1],String(t[C])===String(e[C])):isNaN(t)&&isNaN(e)?!0:Number(t)===Number(e);if(_e(t)&&_e(e)){if(t.length!==e.length)return!1;for(r=i=0,a=t.length-1;a>=0?a>=i:i>=a;r=a>=0?++i:--i)if(!n(t[r],e[r]))return!1;return!0}if(ge(t)&&(ge(e)||null!=e.T))return null!=e.T&&(e=ae(void 0,void 0,void 0,e)),t-0===e-0;if(De(t)&&(De(e)||null!=e.B)){if(null!=e.B&&(e=ae(void 0,void 0,void 0,e)),t.length!==e.length)return!1;for(r=o=0,u=t.length-1;u>=0?u>=o:o>=u;r=u>=0?++o:--o)if(t[r]!==e[r])return!1;return!0}return!1};for(Ce in t)if(tr=t[Ce],i=n(tr,e[Ce]),!i)return i;return!0},I=function(){function t(t){this._datastore=t,this._cache={}}return t.prototype.get=function(t,e){return null==this._cache[t]?null:this._cache[t][e]},t.prototype.getOrCreate=function(t,e){var r;return null==this._cache[t]&&(this._cache[t]={}),r=this._cache[t][e],null==r&&(r=this._cache[t][e]=new p.Datastore.Record(this._datastore,t,e)),r},t.prototype.remove=function(t,e){return delete this._cache[t][e],me(this._cache[t])&&delete this._cache[t],void 0},t}(),D=function(){function t(){this._registered_handlers=[]}return t.prototype.register=function(t,e,r){return t.addListener(e,r),this._registered_handlers.push([t,e,r])},t.prototype.unregister_all=function(){var t,e,r,n,i,o,s,a;for(o=this._registered_handlers,a=[],n=0,i=o.length;i>n;n++)s=o[n],r=s[0],t=s[1],e=s[2],a.push(r.removeListener(t,e));return a},t}(),p.File.ShareUrl=function(){function t(t,e){this.url=t.url,this.expiresAt=p.Util.parseDate(t.expires),this.isDirect=e===!0?!0:e===!1?!1:"direct"in t?t.direct:Date.now()-this.expiresAt<=864e5,this.isPreview=!this.isDirect,this._json=null}return t.parse=function(t,e){return t&&"object"==typeof t?new p.File.ShareUrl(t,e):t},t.prototype.url=null,t.prototype.expiresAt=null,t.prototype.isDirect=null,t.prototype.isPreview=null,t.prototype.json=function(){return this._json||(this._json={url:this.url,expires:this.expiresAt.toUTCString(),direct:this.isDirect})},t}(),p.File.CopyReference=function(){function t(t){"object"==typeof t?(this.tag=t.copy_ref,this.expiresAt=p.Util.parseDate(t.expires),this._json=t):(this.tag=t,this.expiresAt=new Date(1e3*Math.ceil(Date.now()/1e3)),this._json=null)}return t.parse=function(t){return!t||"object"!=typeof t&&"string"!=typeof t?t:new p.File.CopyReference(t)},t.prototype.tag=null,t.prototype.expiresAt=null,t.prototype.json=function(){return this._json||(this._json={copy_ref:this.tag,expires:this.expiresAt.toUTCString()})},t}(),p.File.Stat=function(){function t(t){var e,r,n,i;switch(this._json=t,this.path=t.path,"/"!==this.path.substring(0,1)&&(this.path="/"+this.path),e=this.path.length-1,e>=0&&"/"===this.path.substring(e)&&(this.path=this.path.substring(0,e)),r=this.path.lastIndexOf("/"),this.name=this.path.substring(r+1),this.isFolder=t.is_dir||!1,this.isFile=!this.isFolder,this.isRemoved=t.is_deleted||!1,this.typeIcon=t.icon,this.modifiedAt=(null!=(n=t.modified)?n.length:void 0)?p.Util.parseDate(t.modified):null,this.clientModifiedAt=(null!=(i=t.client_mtime)?i.length:void 0)?p.Util.parseDate(t.client_mtime):null,t.root){case"dropbox":this.inAppFolder=!1;break;case"app_folder":this.inAppFolder=!0;break;default:this.inAppFolder=null}this.size=t.bytes||0,this.humanSize=t.size||"",this.hasThumbnail=t.thumb_exists||!1,this.versionTag=t.rev,this.contentHash=t.hash||null,this.mimeType=this.isFolder?t.mime_type||"inode/directory":t.mime_type||"application/octet-stream"}return t.parse=function(t){return t&&"object"==typeof t?new p.File.Stat(t):t},t.prototype.path=null,t.prototype.name=null,t.prototype.inAppFolder=null,t.prototype.isFolder=null,t.prototype.isFile=null,t.prototype.isRemoved=null,t.prototype.typeIcon=null,t.prototype.versionTag=null,t.prototype.contentHash=null,t.prototype.mimeType=null,t.prototype.size=null,t.prototype.humanSize=null,t.prototype.hasThumbnail=null,t.prototype.modifiedAt=null,t.prototype.clientModifiedAt=null,t.prototype.json=function(){return this._json},t}(),p.Http.PulledChanges=function(){function t(t){var e;this.blankSlate=t.reset||!1,this.cursorTag=t.cursor,this.shouldPullAgain=t.has_more,this.shouldBackOff=!this.shouldPullAgain,this.changes=t.cursor&&t.cursor.length?function(){var r,n,i,o;for(i=t.entries,o=[],r=0,n=i.length;n>r;r++)e=i[r],o.push(p.Http.PulledChange.parse(e));return o}():[]}return t.parse=function(t){return t&&"object"==typeof t?new p.Http.PulledChanges(t):t},t.prototype.blankSlate=void 0,t.prototype.cursorTag=void 0,t.prototype.changes=void 0,t.prototype.shouldPullAgain=void 0,t.prototype.shouldBackOff=void 0,t.prototype.cursor=function(){return this.cursorTag},t}(),p.Http.PulledChange=function(){function t(t){this.path=t[0],this.stat=p.File.Stat.parse(t[1]),this.stat?this.wasRemoved=!1:(this.stat=null,this.wasRemoved=!0)}return t.parse=function(t){return t&&"object"==typeof t?new p.Http.PulledChange(t):t},t.prototype.path=void 0,t.prototype.wasRemoved=void 0,t.prototype.stat=void 0,t}(),p.Http.RangeInfo=function(){function t(t){var e;(e=/^bytes (\d*)-(\d*)\/(.*)$/.exec(t))?(this.start=parseInt(e[1]),this.end=parseInt(e[2]),this.size="*"===e[3]?null:parseInt(e[3])):(this.start=0,this.end=0,this.size=null)}return t.parse=function(t){return"string"==typeof t?new p.Http.RangeInfo(t):t},t.prototype.start=null,t.prototype.size=null,t.prototype.end=null,t}(),p.Http.UploadCursor=function(){function t(t){this.replace(t)}return t.parse=function(t){return!t||"object"!=typeof t&&"string"!=typeof t?t:new p.Http.UploadCursor(t)},t.prototype.tag=null,t.prototype.offset=null,t.prototype.expiresAt=null,t.prototype.json=function(){return this._json||(this._json={upload_id:this.tag,offset:this.offset,expires:this.expiresAt.toUTCString()})},t.prototype.replace=function(t){return"object"==typeof t?(this.tag=t.upload_id||null,this.offset=t.offset||0,this.expiresAt=p.Util.parseDate(t.expires)||Date.now(),this._json=t):(this.tag=t||null,this.offset=0,this.expiresAt=new Date(1e3*Math.floor(Date.now()/1e3)),this._json=null),this},t}(),"function"==typeof V&&"function"==typeof Q?(V=function(t){return window.atob(t)},Q=function(t){return window.btoa(t)}):"undefined"==typeof window&&"undefined"==typeof self||"undefined"==typeof navigator||"string"!=typeof navigator.userAgent?(V=function(t){var e,r;return e=new Buffer(t,"base64"),function(){var t,n,i;for(i=[],r=t=0,n=e.length;n>=0?n>t:t>n;r=n>=0?++t:--t)i.push(String.fromCharCode(e[r]));return i}().join("")},Q=function(t){var e,r;return e=new Buffer(function(){var e,n,i;for(i=[],r=e=0,n=t.length;n>=0?n>e:e>n;r=n>=0?++e:--e)i.push(t.charCodeAt(r));return i}()),e.toString("base64")}):(G="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/",Y=function(t,e,r){var n,i;for(i=3-e,t<<=8*i,n=3;n>=i;)r.push(G.charAt(63&t>>6*n)),n-=1;for(n=e;3>n;)r.push("="),n+=1;return null},J=function(t,e,r){var n,i;for(i=4-e,t<<=6*i,n=2;n>=i;)r.push(String.fromCharCode(255&t>>8*n)),n-=1;return null},Q=function(t){var e,r,n,i,o,s;for(i=[],e=0,r=0,n=o=0,s=t.length;s>=0?s>o:o>s;n=s>=0?++o:--o)e=e<<8|t.charCodeAt(n),r+=1,3===r&&(Y(e,r,i),e=r=0);return r>0&&Y(e,r,i),i.join("")},V=function(t){var e,r,n,i,o,s,a;for(o=[],e=0,n=0,i=s=0,a=t.length;(a>=0?a>s:s>a)&&(r=t.charAt(i),"="!==r);i=a>=0?++s:--s)e=e<<6|G.indexOf(r),n+=1,4===n&&(J(e,n,o),e=n=0);return n>0&&J(e,n,o),o.join("")}),p.Util.atob=V,p.Util.btoa=Q,p.Util.hmac=function(t,e){return q(ue(Je(t),Je(e),t.length,e.length))},p.Util.sha1=function(t){return q(He(Je(t),t.length))},"undefined"!=typeof require)try{ie=require("crypto"),ie.createHmac&&ie.createHash&&(p.Util.hmac=function(t,e){var r;return r=ie.createHmac("sha1",e),r.update(t),r.digest("base64")},p.Util.sha1=function(t){var e;return e=ie.createHash("sha1"),e.update(t),e.digest("base64")})}catch(hr){Xe=hr}if(ue=function(t,e,r,n){var i,o,s,a;return e.length>16&&(e=He(e,n)),s=function(){var t,r;for(r=[],o=t=0;16>t;o=++t)r.push(909522486^e[o]);return r}(),a=function(){var t,r;for(r=[],o=t=0;16>t;o=++t)r.push(1549556828^e[o]);return r}(),i=He(s.concat(t),64+r),He(a.concat(i),84)},He=function(t,e){var r,n,i,o,s,a,u,l,h,c,p,d,f,_,y,g,m,v;for(t[e>>2]|=1<<31-((3&e)<<3),t[(e+8>>6<<4)+15]=e<<3,g=Array(80),r=1732584193,i=-271733879,s=-1732584194,u=271733878,h=-1009589776,d=0,y=t.length;y>d;){for(n=r,o=i,a=s,l=u,c=h,f=v=0;80>v;f=++v)g[f]=16>f?t[d+f]:ze(g[f-3]^g[f-8]^g[f-14]^g[f-16],1),20>f?(p=i&s|~i&u,_=1518500249):40>f?(p=i^s^u,_=1859775393):60>f?(p=i&s|i&u|s&u,_=-1894007588):(p=i^s^u,_=-899497514),m=H(H(ze(r,5),p),H(H(h,g[f]),_)),h=u,u=s,s=ze(i,30),i=r,r=m;r=H(r,n),i=H(i,o),s=H(s,a),u=H(u,l),h=H(h,c),d+=16}return[r,i,s,u,h]},ze=function(t,e){return t<<e|t>>>32-e},H=function(t,e){var r,n;return n=(65535&t)+(65535&e),r=(t>>16)+(e>>16)+(n>>16),r<<16|65535&n},q=function(t){var e,r,n,i,o;for(i="",e=0,n=4*t.length;n>e;)r=e,o=(255&t[r>>2]>>(3-(3&r)<<3))<<16,r+=1,o|=(255&t[r>>2]>>(3-(3&r)<<3))<<8,r+=1,o|=255&t[r>>2]>>(3-(3&r)<<3),i+=nr[63&o>>18],i+=nr[63&o>>12],e+=1,i+=e>=n?"=":nr[63&o>>6],e+=1,i+=e>=n?"=":nr[63&o],e+=1;return i},nr="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/",Je=function(t){var e,r,n,i,o;for(e=[],n=255,r=i=0,o=t.length;o>=0?o>i:i>o;r=o>=0?++i:--i)e[r>>2]|=(t.charCodeAt(r)&n)<<(3-(3&r)<<3);return e},p.Util.Oauth=function(){function t(t){this._id=null,this._secret=null,this._stateParam=null,this._authCode=null,this._token=null,this._tokenKey=null,this._tokenKid=null,this._error=null,this._appHash=null,this._loaded=null,this.setCredentials(t)}return t.prototype.setCredentials=function(t){if(t.key)this._id=t.key;else{if(!t.token)throw new Error("No API key supplied");this._id=null}return this._secret=t.secret||null,this._appHash=null,this._error=null,this._loaded=!0,this.reset(),t.token?(this._token=t.token,t.tokenKey&&(this._tokenKey=t.tokenKey,this._tokenKid=t.tokenKid)):t.oauthCode?this._authCode=t.oauthCode:t.oauthStateParam&&(this._stateParam=t.oauthStateParam),this},t.prototype.credentials=function(){var t;return t={},this._id&&(t.key=this._id),this._secret&&(t.secret=this._secret),null!==this._token?(t.token=this._token,this._tokenKey&&(t.tokenKey=this._tokenKey,t.tokenKid=this._tokenKid)):null!==this._authCode?t.oauthCode=this._authCode:null!==this._stateParam&&(t.oauthStateParam=this._stateParam),t},t.prototype.step=function(){return null!==this._token?p.Client.DONE:null!==this._authCode?p.Client.AUTHORIZED:null!==this._stateParam?this._loaded?p.Client.PARAM_LOADED:p.Client.PARAM_SET:null!==this._error?p.Client.ERROR:p.Client.RESET},t.prototype.setAuthStateParam=function(t){if(null===this._id)throw new Error("No API key supplied, cannot do authorization");return this.reset(),this._loaded=!1,this._stateParam=t,this},t.prototype.checkAuthStateParam=function(t){return this._stateParam===t&&null!==this._stateParam},t.prototype.authStateParam=function(){return this._stateParam},t.prototype.error=function(){return this._error},t.prototype.processRedirectParams=function(t){var e;if(t.error){if(null===this._id)throw new Error("No API key supplied, cannot process errors");return this.reset(),this._error=new p.AuthError(t),!0}if(t.code){if(null===this._id)throw new Error("No API key supplied, cannot do Authorization Codes");return this.reset(),this._loaded=!1,this._authCode=t.code,!0}if(e=t.token_type){if(e=e.toLowerCase(),"bearer"!==e&&"mac"!==e)throw new Error("Unimplemented token type "+e);if(this.reset(),this._loaded=!1,"mac"===e){if("hmac-sha-1"!==t.mac_algorithm)throw new Error("Unimplemented MAC algorithms "+t.mac_algorithm);this._tokenKey=t.mac_key,this._tokenKid=t.kid}return this._token=t.access_token,!0}return!1},t.prototype.authHeader=function(t,e,r){var n,i;return null===this._token?(i=null===this._secret?p.Util.btoa(""+this._id+":"):p.Util.btoa(""+this._id+":"+this._secret),"Basic "+i):null===this._tokenKey?"Bearer "+this._token:(n=this.macParams(t,e,r),"MAC kid="+n.kid+" ts="+n.ts+" "+("access_token="+this._token+" mac="+n.mac))},t.prototype.addAuthParams=function(t,e,r){var n;return null===this._token?(r.client_id=this._id,null!==this._secret&&(r.client_secret=this._secret)):(null!==this._tokenKey&&(n=this.macParams(t,e,r),r.kid=n.kid,r.ts=n.ts,r.mac=n.mac),r.access_token=this._token),r},t.prototype.authorizeUrlParams=function(t,e){var r;if("token"!==t&&"code"!==t)throw new Error("Unimplemented /authorize response type "+t);return r={client_id:this._id,state:this._stateParam,response_type:t},e&&(r.redirect_uri=e),r},t.prototype.accessTokenParams=function(t){var e;return e={grant_type:"authorization_code",code:this._authCode},t&&(e.redirect_uri=t),e},t.queryParamsFromUrl=function(t){var e,r,n,i,o,s,a,u,l,h;if(i=/^[^?#]+(\?([^\#]*))?(\#(.*))?$/.exec(t),!i)return{};for(a=i[2]||"",e=i[4]||"",r=e.indexOf("?"),-1!==r&&(e=e.substring(r+1)),s={},h=a.split("&").concat(e.split("&")),u=0,l=h.length;l>u;u++)n=h[u],o=n.indexOf("="),-1!==o&&(s[decodeURIComponent(n.substring(0,o))]=decodeURIComponent(n.substring(o+1)));return s},t.prototype.macParams=function(t,e,r){var n,i;return n={kid:this._tokenKid,ts:p.Util.Oauth.timestamp()},i=t.toUpperCase()+"&"+p.Util.Xhr.urlEncodeValue(e)+"&"+p.Util.Xhr.urlEncodeValue(p.Util.Xhr.urlEncode(r)),n.mac=p.Util.hmac(i,this._tokenKey),n},t.prototype.appHash=function(){return this._appHash?this._appHash:this._appHash=p.Util.sha1("oauth2-"+this._id).replace(/[\/+=]/g,"")},t.prototype.reset=function(){return this._stateParam=null,this._authCode=null,this._token=null,this._tokenKey=null,this._tokenKid=null,this},t.timestamp=function(){return Math.floor(Date.now()/1e3)},t.randomAuthStateParam=function(){return["oas",Date.now().toString(36),Math.random().toString(36)].join("_")},t}(),null==Date.now&&(p.Util.Oauth.timestamp=function(){return Math.floor((new Date).getTime()/1e3)}),2274814865e3===new Date("Fri, 31 Jan 2042 21:01:05 +0000").valueOf()?je=function(t){return new Date(t)}:2274814865e3===Date.parse("Fri, 31 Jan 2042 21:01:05 +0000")?je=function(t){return new Date(Date.parse(t))}:(Fe=/^\w+\, (\d+) (\w+) (\d+) (\d+)\:(\d+)\:(\d+) (\+\d+|UTC|GMT)$/,Ne={Jan:0,Feb:1,Mar:2,Apr:3,May:4,Jun:5,Jul:6,Aug:7,Sep:8,Oct:9,Nov:10,Dec:11},je=function(t){var e;return(e=Fe.exec(t))?new Date(Date.UTC(parseInt(e[3]),Ne[e[2]],parseInt(e[1]),parseInt(e[4]),parseInt(e[5]),parseInt(e[6]),0)):0/0}),p.Util.parseDate=je,"undefined"==typeof XMLHttpRequest||"undefined"==typeof window&&"undefined"==typeof self||"undefined"==typeof navigator||"string"!=typeof navigator.userAgent?(w=require("xhr2"),v=!1,g=!1,m=!1):("undefined"==typeof XDomainRequest||"withCredentials"in new XMLHttpRequest?(w=XMLHttpRequest,v=!1,g="undefined"!=typeof FormData&&-1===navigator.userAgent.indexOf("Firefox")):(w=XDomainRequest,v=!0,g=!1),m=!0),"undefined"==typeof Uint8Array)y=null,S=!1,b=!1;else if(Object.getPrototypeOf?y=Object.getPrototypeOf(Object.getPrototypeOf(new Uint8Array(0))).constructor:Object.__proto__&&(y=new Uint8Array(0).__proto__.__proto__.constructor),"undefined"==typeof Blob)S=!1,b=!0;else{try{2===new Blob([new Uint8Array(2)]).size?(S=!0,b=!0):(b=!1,S=2===new Blob([new ArrayBuffer(2)]).size)}catch(hr){Z=hr,b=!1,S=!1,"undefined"!=typeof WebKitBlobBuilder&&-1!==navigator.userAgent.indexOf("Android")&&(g=!1)}y===Object&&(b=!1)}p.Util.Xhr=function(){function t(t,e){this.method=t,this.isGet="GET"===this.method,this.url=e,this.wantHeaders=!1,this.headers={},this.params=null,this.body=null,this.preflight=!(this.isGet||"POST"===this.method),this.signed=!1,this.completed=!1,this.responseType=null,this.callback=null,this.xhr=null,this.onError=null}return t.Request=w,t.ieXdr=v,t.canSendForms=g,t.doesPreflight=m,t.ArrayBufferView=y,t.sendArrayBufferView=b,t.wrapBlob=S,t.prototype.xhr=null,t.prototype.onError=null,t.prototype.setParams=function(t){if(this.signed)throw new Error("setParams called after addOauthParams or addOauthHeader");if(this.params)throw new Error("setParams cannot be called twice");return this.params=t,this},t.prototype.setCallback=function(t){return this.callback=t,this},t.prototype.signWithOauth=function(t,e){return p.Util.Xhr.ieXdr?this.addOauthParams(t):this.preflight||!p.Util.Xhr.doesPreflight?this.addOauthHeader(t):this.isGet&&e?this.addOauthHeader(t):this.addOauthParams(t)},t.prototype.addOauthParams=function(t){if(this.signed)throw new Error("Request already has an OAuth signature");return this.params||(this.params={}),t.addAuthParams(this.method,this.url,this.params),this.signed=!0,this},t.prototype.addOauthHeader=function(t){if(this.signed)throw new Error("Request already has an OAuth signature");return this.params||(this.params={}),this.signed=!0,this.setHeader("Authorization",t.authHeader(this.method,this.url,this.params))},t.prototype.setBody=function(t){if(this.isGet)throw new Error("setBody cannot be called on GET requests");if(null!==this.body)throw new Error("Request already has a body");return"string"==typeof t||"undefined"!=typeof FormData&&t instanceof FormData||(this.headers["Content-Type"]="application/octet-stream",this.preflight=!0),this.body=t,this},t.prototype.setResponseType=function(t){return this.responseType=t,this},t.prototype.setHeader=function(t,e){var r;if(this.headers[t])throw r=this.headers[t],new Error("HTTP header "+t+" already set to "+r);if("Content-Type"===t)throw new Error("Content-Type is automatically computed based on setBody");return this.preflight=!0,this.headers[t]=e,this},t.prototype.reportResponseHeaders=function(){return this.wantHeaders=!0},t.prototype.setFileField=function(t,e,r,n){var i,o,s,a;if(null!==this.body)throw new Error("Request already has a body");if(this.isGet)throw new Error("setFileField cannot be called on GET requests");if("object"==typeof r){"undefined"!=typeof ArrayBuffer&&(r instanceof ArrayBuffer?p.Util.Xhr.sendArrayBufferView&&(r=new Uint8Array(r)):!p.Util.Xhr.sendArrayBufferView&&0===r.byteOffset&&r.buffer instanceof ArrayBuffer&&(r=r.buffer)),n||(n="application/octet-stream");try{r=new Blob([r],{type:n})}catch(u){Z=u,window.WebKitBlobBuilder&&(s=new WebKitBlobBuilder,s.append(r),(i=s.getBlob(n))&&(r=i))}"undefined"!=typeof File&&r instanceof File&&(r=new Blob([r],{type:r.type})),a=r instanceof Blob}else a=!1;return a?(this.body=new FormData,this.body.append(t,r,e)):(n||(n="application/octet-stream"),o=this.multipartBoundary(),this.headers["Content-Type"]="multipart/form-data; boundary="+o,this.body=["--",o,"\r\n",'Content-Disposition: form-data; name="',t,'"; filename="',e,'"\r\n',"Content-Type: ",n,"\r\n","Content-Transfer-Encoding: binary\r\n\r\n",r,"\r\n","--",o,"--","\r\n"].join(""))},t.prototype.multipartBoundary=function(){return[Date.now().toString(36),Math.random().toString(36)].join("----")},t.prototype.paramsToUrl=function(){var t;return this.params&&(t=p.Util.Xhr.urlEncode(this.params),0!==t.length&&(this.url=[this.url,"?",t].join("")),this.params=null),this},t.prototype.paramsToBody=function(){if(this.params){if(null!==this.body)throw new Error("Request already has a body");if(this.isGet)throw new Error("paramsToBody cannot be called on GET requests");this.headers["Content-Type"]="application/x-www-form-urlencoded",this.body=p.Util.Xhr.urlEncode(this.params),this.params=null}return this},t.prototype.prepare=function(){var t,e,r,n,i=this;if(e=p.Util.Xhr.ieXdr,this.isGet||null!==this.body||e?(this.paramsToUrl(),null!==this.body&&"string"==typeof this.body&&(this.headers["Content-Type"]="text/plain; charset=utf8")):this.paramsToBody(),this.xhr=new p.Util.Xhr.Request,e?(this.xhr.onload=function(){return i.onXdrLoad()},this.xhr.onerror=function(){return i.onXdrError()},this.xhr.ontimeout=function(){return i.onXdrError()},this.xhr.onprogress=function(){}):this.xhr.onreadystatechange=function(){return i.onReadyStateChange()},this.xhr.open(this.method,this.url,!0),!e){n=this.headers;for(t in n)ar.call(n,t)&&(r=n[t],this.xhr.setRequestHeader(t,r))}return this.responseType&&("b"===this.responseType?this.xhr.overrideMimeType&&this.xhr.overrideMimeType("text/plain; charset=x-user-defined"):this.xhr.responseType=this.responseType),this},t.prototype.send=function(t){var e,r;if(this.callback=t||this.callback,null!==this.body){e=this.body,p.Util.Xhr.sendArrayBufferView?e instanceof ArrayBuffer&&(e=new Uint8Array(e)):0===e.byteOffset&&e.buffer instanceof ArrayBuffer&&(e=e.buffer);try{this.xhr.send(e)}catch(n){if(r=n,p.Util.Xhr.sendArrayBufferView||!p.Util.Xhr.wrapBlob)throw r;e=new Blob([e],{type:"application/octet-stream"}),this.xhr.send(e)}}else this.xhr.send();return this},t.urlEncode=function(t){var e,r,n;e=[];for(r in t)n=t[r],e.push(this.urlEncodeValue(r)+"="+this.urlEncodeValue(n));return e.sort().join("&")},t.urlEncodeValue=function(t){return encodeURIComponent(t.toString()).replace(/\!/g,"%21").replace(/'/g,"%27").replace(/\(/g,"%28").replace(/\)/g,"%29").replace(/\*/g,"%2A")},t.urlDecode=function(t){var e,r,n,i,o,s;for(r={},s=t.split("&"),i=0,o=s.length;o>i;i++)n=s[i],e=n.split("="),r[decodeURIComponent(e[0])]=decodeURIComponent(e[1]);return r},t.prototype.onReadyStateChange=function(){var t,e,r,n,i,o,s,a,u,l,h,c,d,f;if(4!==this.xhr.readyState)return!0;if(this.completed)return!0;if(this.completed=!0,this.xhr.status<200||this.xhr.status>=300)return e=new p.ApiError(this.xhr,this.method,this.url),this.onError?this.onError(e,this.callback):this.callback(e),!0;if(this.wantHeaders?(t=this.xhr.getAllResponseHeaders(),o=t?p.Util.Xhr.parseResponseHeaders(t):this.guessResponseHeaders(),l=o["x-dropbox-metadata"]):(o=void 0,l=this.xhr.getResponseHeader("x-dropbox-metadata")),null!=l?l.length:void 0)try{u=JSON.parse(l)}catch(_){a=_,u=void 0}else u=void 0;if(this.responseType){if("b"===this.responseType){for(i=null!=this.xhr.responseText?this.xhr.responseText:this.xhr.response,r=[],s=d=0,f=i.length;f>=0?f>d:d>f;s=f>=0?++d:--d)r.push(String.fromCharCode(255&i.charCodeAt(s)));c=r.join(""),this.callback(null,c,u,o)}else this.callback(null,this.xhr.response,u,o);return!0}switch(c=null!=this.xhr.responseText?this.xhr.responseText:this.xhr.response,n=this.xhr.getResponseHeader("Content-Type"),n&&(h=n.indexOf(";"),-1!==h&&(n=n.substring(0,h))),n){case"application/x-www-form-urlencoded":this.callback(null,p.Util.Xhr.urlDecode(c),u,o);break;case"application/json":case"text/javascript":this.callback(null,JSON.parse(c),u,o);break;default:this.callback(null,c,u,o)}return!0},t.parseResponseHeaders=function(t){var e,r,n,i,o,s,a,u;for(n={},r=t.split("\n"),a=0,u=r.length;u>a;a++)i=r[a],e=i.indexOf(":"),o=i.substring(0,e).trim().toLowerCase(),s=i.substring(e+1).trim(),n[o]=s;return n},t.prototype.guessResponseHeaders=function(){var t,e,r,n,i,o;for(t={},o=["cache-control","content-language","content-range","content-type","expires","last-modified","pragma","x-dropbox-metadata"],n=0,i=o.length;i>n;n++)e=o[n],r=this.xhr.getResponseHeader(e),r&&(t[e]=r);return t},t.prototype.onXdrLoad=function(){var t,e,r;if(this.completed)return!0;if(this.completed=!0,r=this.xhr.responseText,t=this.wantHeaders?{"content-type":this.xhr.contentType}:void 0,e=void 0,this.responseType)return this.callback(null,r,e,t),!0;switch(this.xhr.contentType){case"application/x-www-form-urlencoded":this.callback(null,p.Util.Xhr.urlDecode(r),e,t);break;case"application/json":case"text/javascript":this.callback(null,JSON.parse(r),e,t);break;default:this.callback(null,r,e,t)}return!0},t.prototype.onXdrError=function(){var t;return this.completed?!0:(this.completed=!0,t=new p.ApiError(this.xhr,this.method,this.url),this.onError?this.onError(t,this.callback):this.callback(t),!0)},t}(),p.DatastoresClient={_listDatastores:function(t){var e;return e=new p.Util.Xhr("GET",this.urls.listDbs),e.signWithOauth(this.oauth),this.dispatchXhr(e,function(e,r){var n,i;return e?t(e):(i=r&&r.dbs?function(){var t,e,i,o;for(i=r.dbs,o=[],t=0,e=i.length;e>t;t++)n=i[t],o.push(p.Datastore.Stat.parse(n));return o}():null,t(null,i))})},_getOrCreateDatastore:function(t,e){var r;return r=new p.Util.Xhr("POST",this.urls.getOrCreateDb),r.setParams({path:t}).signWithOauth(this.oauth),this.dispatchXhr(r,function(r,n){return r?e(r):e(null,p.Datastore.Stat.parse(n,t),n.created)})},_getDatastore:function(t,e){var r;return r=new p.Util.Xhr("GET",this.urls.getDb),r.setParams({path:t}).signWithOauth(this.oauth),this.dispatchXhr(r,function(r,n){return r?e(r):e(null,p.Datastore.Stat.parse(n,t))})},_deleteDatastoreByPath:function(t,e){var r;return r=new p.Util.Xhr("POST",this.urls.deleteDb),r.setParams({path:t}),r.signWithOauth(this.oauth,!1),this.dispatchXhr(r,function(t){return e(t)})},_getDeltas:function(t,e,r){var n;return n=new p.Util.Xhr("GET",this.urls.getDeltas),n.setParams({dbid:t,rev:e}).signWithOauth(this.oauth),this.dispatchXhr(n,function(t,e){return t?r(t):r(null,sequence,!!e.more)})},_putDelta:function(t,e,r){var n;return n=new p.Util.Xhr("POST",this.urls.putDelta),n.setParams({dbid:t,rev:e.revision,nonce:e.nonce,metadata:e.metadata,changes:JSON.stringify(e.changes)}).signWithOauth(this.oauth),this.dispatchXhr(n,function(t){return r(t)})},_getSnapshot:function(t,e){var r;return r=new p.Util.Xhr("GET",this.urls.getSnapshot),r.setParams({dbid:t}).signWithOauth(this.oauth),this.dispatchXhr(r,function(r,n){return r?e(r):e(null,p.Datastore.Snapshot.parse(n,t))})},_datastoreAwait:function(t,e,r){var n;return n=new p.Util.Xhr("GET",this.urls.datastoreAwait),n.setParams({cursors:JSON.stringify(t),listdbs:JSON.stringify({token:e})}).signWithOauth(this.oauth),this.dispatchLongPollXhr(n,function(t,e){return r(t,e)})},getDatastoreManager:function(){var t,e=this;return null==this._datastoreManager&&(this._datastoreManager=new p.Datastore.DatastoreManager(this),t=function(){return e.authStep===p.Client.SIGNED_OUT?(e._datastoreManager.close(),e._datastoreManager=null,e.onAuthStepChange.removeListener(t)):void 0},this.onAuthStepChange.addListener(t)),this._datastoreManager},openDefaultDatastore:function(t){return this.getDatastoreManager().openDefaultDatastore(t)},deleteDefaultDatastore:function(t){return this.getDatastoreManager().deleteDefaultDatastore(t)}},or=p.DatastoresClient;for(Re in or)ke=or[Re],p.Client.prototype[Re]=ke;if("undefined"!=typeof module&&"exports"in module)module.exports=p;else if("undefined"!=typeof window&&null!==window)if(window.Dropbox)for(Ie in p)ar.call(p,Ie)&&(rr=p[Ie],window.Dropbox[Ie]=rr);else window.Dropbox=p;else{if("undefined"==typeof self||null===self)throw new Error("This library only supports node.js and modern browsers.");self.Dropbox=p}p.File.PublicUrl=p.File.ShareUrl,p.UserInfo=p.AccountInfo}.call(this);

define("dropbox-datastore", (function (global) {
    return function () {
        var ret, fn;
        return ret || global.dropbox-datastore;
    };
}(this)));

define('config',[], function() {
	var config = {};
	config.apiKey = 'lfksu2l4dhmimfm';
	//config.apiSecret = 'qgano5n2v6t9dq4';
  
	_.templateSettings = {
		interpolate: /\{\{(.+?)\}\}/g
	};
  
	return config;
});

// see https://developers.google.com/drive/auth/web-client;
define('gapi',['config'], function(config) {
	var app
	, client = new Dropbox.Client({key: config.apiKey});

	function ApiManager(_app) {
		app = _app;
		this.loadGapi();
	}

	_.extend(ApiManager.prototype, Backbone.Events);

	ApiManager.prototype.init = function() {
		var that = this;
	};

	ApiManager.prototype.loadGapi = function() {
		var that = this;
		client.authenticate();
		
		if ( client.isAuthenticated() ) {
			this.dataStoreManager = client.getDatastoreManager();
			//this.trigger('loaded');
		}
	};
	
	Backbone.sync = function(method, model, options) {

		switch(method) {	
			case 'read':
				request = app.dataStore.getTable(model.url);				
				Backbone.gapiRequest(request, method, model, options);
			break;
		}
	};
	
	Backbone.gapiRequest = function(request, method, model, options) {
		var records
		, data
		;
		records = request.query();
		
		for (var i = 0; i < records.length; i++) {
			var record = records[i], rec;
			rec = record.getFields();
			rec.id = record.getId();
			//model.add(rec); // adds the records to the collection
			options.success(model, rec, options)
			
			/*$('body').append(
					record.getId(),
					record.get('completed'),
					record.get('taskname'),
					record.get('created')
				);
			*/
		}
		
		//options.success(model, rec, options)
		
	};
	
	return ApiManager;
});

define('models/task',[],function() {
	var Task = Backbone.Model.extend({
		//url: 'tasks',
		//defaults: { title: '', notes: '' }
	});

	return Task;
});
define('collections/tasklists',['models/task'], function(Task) {
	
	var TaskLists = Backbone.Collection.extend({
		model: Task
		, url: 'tasks'
	});

	return TaskLists;
});
/**
 * @license RequireJS text 2.0.10 Copyright (c) 2010-2012, The Dojo Foundation All Rights Reserved.
 * Available via the MIT or new BSD license.
 * see: http://github.com/requirejs/text for details
 */
/*jslint regexp: true */
/*global require, XMLHttpRequest, ActiveXObject,
  define, window, process, Packages,
  java, location, Components, FileUtils */

define('text',['module'], function (module) {
    

    var text, fs, Cc, Ci, xpcIsWindows,
        progIds = ['Msxml2.XMLHTTP', 'Microsoft.XMLHTTP', 'Msxml2.XMLHTTP.4.0'],
        xmlRegExp = /^\s*<\?xml(\s)+version=[\'\"](\d)*.(\d)*[\'\"](\s)*\?>/im,
        bodyRegExp = /<body[^>]*>\s*([\s\S]+)\s*<\/body>/im,
        hasLocation = typeof location !== 'undefined' && location.href,
        defaultProtocol = hasLocation && location.protocol && location.protocol.replace(/\:/, ''),
        defaultHostName = hasLocation && location.hostname,
        defaultPort = hasLocation && (location.port || undefined),
        buildMap = {},
        masterConfig = (module.config && module.config()) || {};

    text = {
        version: '2.0.10',

        strip: function (content) {
            //Strips <?xml ...?> declarations so that external SVG and XML
            //documents can be added to a document without worry. Also, if the string
            //is an HTML document, only the part inside the body tag is returned.
            if (content) {
                content = content.replace(xmlRegExp, "");
                var matches = content.match(bodyRegExp);
                if (matches) {
                    content = matches[1];
                }
            } else {
                content = "";
            }
            return content;
        },

        jsEscape: function (content) {
            return content.replace(/(['\\])/g, '\\$1')
                .replace(/[\f]/g, "\\f")
                .replace(/[\b]/g, "\\b")
                .replace(/[\n]/g, "\\n")
                .replace(/[\t]/g, "\\t")
                .replace(/[\r]/g, "\\r")
                .replace(/[\u2028]/g, "\\u2028")
                .replace(/[\u2029]/g, "\\u2029");
        },

        createXhr: masterConfig.createXhr || function () {
            //Would love to dump the ActiveX crap in here. Need IE 6 to die first.
            var xhr, i, progId;
            if (typeof XMLHttpRequest !== "undefined") {
                return new XMLHttpRequest();
            } else if (typeof ActiveXObject !== "undefined") {
                for (i = 0; i < 3; i += 1) {
                    progId = progIds[i];
                    try {
                        xhr = new ActiveXObject(progId);
                    } catch (e) {}

                    if (xhr) {
                        progIds = [progId];  // so faster next time
                        break;
                    }
                }
            }

            return xhr;
        },

        /**
         * Parses a resource name into its component parts. Resource names
         * look like: module/name.ext!strip, where the !strip part is
         * optional.
         * @param {String} name the resource name
         * @returns {Object} with properties "moduleName", "ext" and "strip"
         * where strip is a boolean.
         */
        parseName: function (name) {
            var modName, ext, temp,
                strip = false,
                index = name.indexOf("."),
                isRelative = name.indexOf('./') === 0 ||
                             name.indexOf('../') === 0;

            if (index !== -1 && (!isRelative || index > 1)) {
                modName = name.substring(0, index);
                ext = name.substring(index + 1, name.length);
            } else {
                modName = name;
            }

            temp = ext || modName;
            index = temp.indexOf("!");
            if (index !== -1) {
                //Pull off the strip arg.
                strip = temp.substring(index + 1) === "strip";
                temp = temp.substring(0, index);
                if (ext) {
                    ext = temp;
                } else {
                    modName = temp;
                }
            }

            return {
                moduleName: modName,
                ext: ext,
                strip: strip
            };
        },

        xdRegExp: /^((\w+)\:)?\/\/([^\/\\]+)/,

        /**
         * Is an URL on another domain. Only works for browser use, returns
         * false in non-browser environments. Only used to know if an
         * optimized .js version of a text resource should be loaded
         * instead.
         * @param {String} url
         * @returns Boolean
         */
        useXhr: function (url, protocol, hostname, port) {
            var uProtocol, uHostName, uPort,
                match = text.xdRegExp.exec(url);
            if (!match) {
                return true;
            }
            uProtocol = match[2];
            uHostName = match[3];

            uHostName = uHostName.split(':');
            uPort = uHostName[1];
            uHostName = uHostName[0];

            return (!uProtocol || uProtocol === protocol) &&
                   (!uHostName || uHostName.toLowerCase() === hostname.toLowerCase()) &&
                   ((!uPort && !uHostName) || uPort === port);
        },

        finishLoad: function (name, strip, content, onLoad) {
            content = strip ? text.strip(content) : content;
            if (masterConfig.isBuild) {
                buildMap[name] = content;
            }
            onLoad(content);
        },

        load: function (name, req, onLoad, config) {
            //Name has format: some.module.filext!strip
            //The strip part is optional.
            //if strip is present, then that means only get the string contents
            //inside a body tag in an HTML string. For XML/SVG content it means
            //removing the <?xml ...?> declarations so the content can be inserted
            //into the current doc without problems.

            // Do not bother with the work if a build and text will
            // not be inlined.
            if (config.isBuild && !config.inlineText) {
                onLoad();
                return;
            }

            masterConfig.isBuild = config.isBuild;

            var parsed = text.parseName(name),
                nonStripName = parsed.moduleName +
                    (parsed.ext ? '.' + parsed.ext : ''),
                url = req.toUrl(nonStripName),
                useXhr = (masterConfig.useXhr) ||
                         text.useXhr;

            // Do not load if it is an empty: url
            if (url.indexOf('empty:') === 0) {
                onLoad();
                return;
            }

            //Load the text. Use XHR if possible and in a browser.
            if (!hasLocation || useXhr(url, defaultProtocol, defaultHostName, defaultPort)) {
                text.get(url, function (content) {
                    text.finishLoad(name, parsed.strip, content, onLoad);
                }, function (err) {
                    if (onLoad.error) {
                        onLoad.error(err);
                    }
                });
            } else {
                //Need to fetch the resource across domains. Assume
                //the resource has been optimized into a JS module. Fetch
                //by the module name + extension, but do not include the
                //!strip part to avoid file system issues.
                req([nonStripName], function (content) {
                    text.finishLoad(parsed.moduleName + '.' + parsed.ext,
                                    parsed.strip, content, onLoad);
                });
            }
        },

        write: function (pluginName, moduleName, write, config) {
            if (buildMap.hasOwnProperty(moduleName)) {
                var content = text.jsEscape(buildMap[moduleName]);
                write.asModule(pluginName + "!" + moduleName,
                               "define(function () { return '" +
                                   content +
                               "';});\n");
            }
        },

        writeFile: function (pluginName, moduleName, req, write, config) {
            var parsed = text.parseName(moduleName),
                extPart = parsed.ext ? '.' + parsed.ext : '',
                nonStripName = parsed.moduleName + extPart,
                //Use a '.js' file name so that it indicates it is a
                //script that can be loaded across domains.
                fileName = req.toUrl(parsed.moduleName + extPart) + '.js';

            //Leverage own load() method to load plugin value, but only
            //write out values that do not have the strip argument,
            //to avoid any potential issues with ! in file names.
            text.load(nonStripName, req, function (value) {
                //Use own write() method to construct full module value.
                //But need to create shell that translates writeFile's
                //write() to the right interface.
                var textWrite = function (contents) {
                    return write(fileName, contents);
                };
                textWrite.asModule = function (moduleName, contents) {
                    return write.asModule(moduleName, fileName, contents);
                };

                text.write(pluginName, nonStripName, textWrite, config);
            }, config);
        }
    };

    if (masterConfig.env === 'node' || (!masterConfig.env &&
            typeof process !== "undefined" &&
            process.versions &&
            !!process.versions.node &&
            !process.versions['node-webkit'])) {
        //Using special require.nodeRequire, something added by r.js.
        fs = require.nodeRequire('fs');

        text.get = function (url, callback, errback) {
            try {
                var file = fs.readFileSync(url, 'utf8');
                //Remove BOM (Byte Mark Order) from utf8 files if it is there.
                if (file.indexOf('\uFEFF') === 0) {
                    file = file.substring(1);
                }
                callback(file);
            } catch (e) {
                errback(e);
            }
        };
    } else if (masterConfig.env === 'xhr' || (!masterConfig.env &&
            text.createXhr())) {
        text.get = function (url, callback, errback, headers) {
            var xhr = text.createXhr(), header;
            xhr.open('GET', url, true);

            //Allow plugins direct access to xhr headers
            if (headers) {
                for (header in headers) {
                    if (headers.hasOwnProperty(header)) {
                        xhr.setRequestHeader(header.toLowerCase(), headers[header]);
                    }
                }
            }

            //Allow overrides specified in config
            if (masterConfig.onXhr) {
                masterConfig.onXhr(xhr, url);
            }

            xhr.onreadystatechange = function (evt) {
                var status, err;
                //Do not explicitly handle errors, those should be
                //visible via console output in the browser.
                if (xhr.readyState === 4) {
                    status = xhr.status;
                    if (status > 399 && status < 600) {
                        //An http 4xx or 5xx error. Signal an error.
                        err = new Error(url + ' HTTP status: ' + status);
                        err.xhr = xhr;
                        errback(err);
                    } else {
                        callback(xhr.responseText);
                    }

                    if (masterConfig.onXhrComplete) {
                        masterConfig.onXhrComplete(xhr, url);
                    }
                }
            };
            xhr.send(null);
        };
    } else if (masterConfig.env === 'rhino' || (!masterConfig.env &&
            typeof Packages !== 'undefined' && typeof java !== 'undefined')) {
        //Why Java, why is this so awkward?
        text.get = function (url, callback) {
            var stringBuffer, line,
                encoding = "utf-8",
                file = new java.io.File(url),
                lineSeparator = java.lang.System.getProperty("line.separator"),
                input = new java.io.BufferedReader(new java.io.InputStreamReader(new java.io.FileInputStream(file), encoding)),
                content = '';
            try {
                stringBuffer = new java.lang.StringBuffer();
                line = input.readLine();

                // Byte Order Mark (BOM) - The Unicode Standard, version 3.0, page 324
                // http://www.unicode.org/faq/utf_bom.html

                // Note that when we use utf-8, the BOM should appear as "EF BB BF", but it doesn't due to this bug in the JDK:
                // http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=4508058
                if (line && line.length() && line.charAt(0) === 0xfeff) {
                    // Eat the BOM, since we've already found the encoding on this file,
                    // and we plan to concatenating this buffer with others; the BOM should
                    // only appear at the top of a file.
                    line = line.substring(1);
                }

                if (line !== null) {
                    stringBuffer.append(line);
                }

                while ((line = input.readLine()) !== null) {
                    stringBuffer.append(lineSeparator);
                    stringBuffer.append(line);
                }
                //Make sure we return a JavaScript string and not a Java string.
                content = String(stringBuffer.toString()); //String
            } finally {
                input.close();
            }
            callback(content);
        };
    } else if (masterConfig.env === 'xpconnect' || (!masterConfig.env &&
            typeof Components !== 'undefined' && Components.classes &&
            Components.interfaces)) {
        //Avert your gaze!
        Cc = Components.classes,
        Ci = Components.interfaces;
        Components.utils['import']('resource://gre/modules/FileUtils.jsm');
        xpcIsWindows = ('@mozilla.org/windows-registry-key;1' in Cc);

        text.get = function (url, callback) {
            var inStream, convertStream, fileObj,
                readData = {};

            if (xpcIsWindows) {
                url = url.replace(/\//g, '\\');
            }

            fileObj = new FileUtils.File(url);

            //XPCOM, you so crazy
            try {
                inStream = Cc['@mozilla.org/network/file-input-stream;1']
                           .createInstance(Ci.nsIFileInputStream);
                inStream.init(fileObj, 1, 0, false);

                convertStream = Cc['@mozilla.org/intl/converter-input-stream;1']
                                .createInstance(Ci.nsIConverterInputStream);
                convertStream.init(inStream, "utf-8", inStream.available(),
                Ci.nsIConverterInputStream.DEFAULT_REPLACEMENT_CHARACTER);

                convertStream.readString(inStream.available(), readData);
                convertStream.close();
                inStream.close();
                callback(readData.value);
            } catch (e) {
                throw new Error((fileObj && fileObj.path || '') + ': ' + e);
            }
        };
    }
    return text;
});

define('text!templates/scaffold.html',[],function () { return '<div id="container">\r\n\t<h1>Hello, data</h1>\r\n\t<h4>&nbsp;<span class="label label-danger">coming soon <span class="glyphicon glyphicon-asterisk"></span></span></h4>\r\n</div>';});

define('views/app',[
  'text!templates/scaffold.html'
],

function(template) {
  var AppView = Backbone.View.extend({  // change the name here
    tagName: 'div',
    //className: 'list-menu-item',

    template: _.template(template),

	initialize: function() {
		//this.collection.on('add', this.render, this);
		//this.model.on('destroy', this.remove, this);
		// console.dir(this);
    },
	
    events: {
		//'click .edit-call'	: 'open'
    },
	
	bindings: {
		'.taskid': {
		  observe: 'id'
		}
	},
	
    render: function() {
		var that = this;
		
		//console.dir( this.template() );
		
		this.$el.html( this.template() );
		
		// set up the stickit binding
		//that.stickit();
	
		return this;
    }
	
  });

  return AppView;
});

define('app',[
 'jquery'
 ,'backbone'
 ,'gapi'
 ,'collections/tasklists'
 ,'views/app'
], 

function($, Backbone, ApiManager, TaskLists, AppView) {
	var App = function(ApiManager) {
	
		// global event dispatcher
		this.dispatcher = _.extend({}, Backbone.Events);

		this.connectGapi();
		this.collections.taskList = new TaskLists();
		this.views.appView = new AppView();
	};

	App.prototype = {
		views: {},
		collections: {},
		models: {},
		variables: {},
		connectGapi: function() {
			var that = this
			;
			this.apiManager = new ApiManager(this);
			
			if (this.apiManager.dataStoreManager) {				
				this.apiManager.dataStoreManager.openDefaultDatastore(function (error, dataStore) {
					if (error) {
						console.dir('Error opening default datastore: ' + error);
					}
					
					var container = that.views.appView.render().el;
					$('body')
						.hide()
						.html(container)
						.fadeIn(500);
					
					// Now you have datastores. 
					that.dataStore = dataStore;
					that.collections.taskList.fetch({
						//success: function(model, response){ that.views.appView.render().el;	}
					});
					
					/*that.collections.taskList.on('sync', function(collection, xhr, options){
						that.views.taskView.render().el;
						console.dir(collection);
					});*/
					
					that.taskTable = dataStore.getTable('tasks');
					//that.filesTable = dataStore.getTable('files');
					
					/*var firstTask = that.taskTable.insert({
						taskname: 'Buy milk',
						completed: false,
						created: new Date()
					});*/
				});
			}
		}
	};

	return App;
});