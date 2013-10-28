({
  mainConfigFile: 'js/main.js',
  baseUrl: 'js',
  name: 'main',
  out: 'dist/main.js',
  removedCombined: true,
  findNestedDependencies: true,
  generateSourceMaps: true,
  preserveLicenseComments: false,
  optimize: "uglify2",
  include: 'require',
  uglify2: {
        //Example of a specialized config. If you are fine
        //with the default options, no need to specify
        //any of these properties.
        output: {
            beautify: false
        },
        compress: {
            sequences: true,
            global_defs: {
                DEBUG: false
            }
        },
	report: 'gzip',
	warnings: false,
	mangle: true,
	version: true
    }

})