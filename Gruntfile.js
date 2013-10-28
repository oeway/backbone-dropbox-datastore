function lastModified(minutes) {
  return function(filepath) {
    var filemod = (require('fs').statSync(filepath)).mtime;
    var timeago = (new Date()).setDate((new Date()).getMinutes() - minutes);
    return (filemod > timeago);
  }
}

module.exports = function(grunt) {
	grunt.initConfig({
	pkg: grunt.file.readJSON('package.json'),
		jshint: {
			options: {
				force: true,
				laxbreak: true, 
				laxcomma: true, 
				// reporterOutput: true, // not working
				globals: {
					jQuery: true
				}
			},
			all: {
				src: ['js/*.js'],
				filter: lastModified(24 * 60) // one day ago
			},
		},	
		less: {
			development: {
				options: {
					paths: ["js/lib/bootstrap/less/"],
					yuicompress: false
				},
				files: {
					"css/bootstrap.css": "js/lib/bootstrap/less/bootstrap.less"
				}
			}
		},
		
		cssmin: {
			minify: {
				expand: true,
				cwd: 'dist/',
				src: ['*.css', '!*.min.css'],
				dest: 'dist/',
				ext: '.min.css'
			}
		},
		
		concat: {
			options: {
				separator: ';'
			},
			dist: {	
				src: ['css/*.css', 'js/lib/animo.js/animate+animo.css'],
				dest: 'dist/concat.css'
			}
		}		
});
  
  grunt.loadNpmTasks('grunt-contrib-jshint');
  grunt.loadNpmTasks('grunt-contrib-less');
  grunt.loadNpmTasks('grunt-contrib-concat');
  grunt.loadNpmTasks('grunt-contrib-cssmin');
  grunt.registerTask('default', ['jshint']);
  grunt.registerTask('css', ['less', 'concat', 'cssmin']);
};