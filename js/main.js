requirejs.config({
  baseUrl: 'js',
  
  //urlArgs: "bust=" + (new Date()).getTime(),  // http://stackoverflow.com/a/8479953/578667
  urlArgs: "bust=" + "v1",
  
  paths: { // requirejs-plugins
    'text'					:	'lib/requirejs-text/text'
	, 'font'				:	'lib/requirejs-plugins/src/font'
	, 'propertyParser'	:	'lib/requirejs-plugins/src/propertyParser'
	, 'jquery'			:	'lib/jquery/jquery.min'
	, 'underscore'		:	'lib/lodash/dist/lodash.underscore.min'
	, 'backbone'			:	'lib/backbone/backbone-min'
	, 'stickit'			:	'lib/backbone.stickit/backbone.stickit'
	, 'datastore'		:	'lib/dropbox-datastore/dropbox-datastores-1.0-latest'
	, 'serializeForm'	:	'lib/jquery-serializeForm/src/serializeForm'	
	, 'moment'			:	'lib/momentjs/moment'
	, 'app'				:	'app'
  },

  shim: {
    'underscore': {
		exports: '_'
    },
    'backbone': {
		deps: ['jquery', 'underscore']
		, exports: 'Backbone'
    },
	'stickit': {
		deps: ['backbone'] // http://jsfiddle.net/tednaleid/zJYGv/
		, exports: 'Backbone.Stickit'
	},
	'datastore': {
		deps: ['jquery']
		, exports: 'datastore'
	},
	'serializeForm': {
		deps: ['jquery']
		, exports: 'serializeForm'
	},
    'app': {
		deps: [/*'jquery', 'underscore', 'backbone', */'stickit', 'moment', 'datastore', 'serializeForm']
		, exports: 'app'
    }
  }
});

requirejs([
	'app', 'ga'
],

function(App, registerGoogleAnalytics) {
	window.dStore = new App();
	window.ga = new registerGoogleAnalytics('41587087');
});
