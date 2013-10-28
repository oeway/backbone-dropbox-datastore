define(function(app) {

	var Routes = Backbone.Router.extend({
		
		initialize: function(options) {
			// Matches #page/10, passing "10"
			//this.route("page/:number", "page", function(number){ ... });

			// Matches /117-a/b/c/open, passing "117-a/b/c" to this.open
			//this.route(/^(.*?)\/open$/, "open");
			//this.apiManager = options.apiManager;
			this.dispatcher = options.dispatcher;
			//console.dir(this);
		},

		routes: {
			'*filter': 'setFilter'
		},

		setFilter: function( param ) {
		// Set the current filter to be used
			if (param) {
				param = param.trim();
			}
			
			// console.dir(param);
			// Trigger a collection filter event, causing hiding/unhiding
			this.dispatcher.trigger('filter', param);
		}
	});
  
	return Routes;

  });