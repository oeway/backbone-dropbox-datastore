define([
  'text!templates/navbar.html'
],

function(navbar) {
	var navbarView = Backbone.View.extend({  // change the name here

		navBarTemplate: _.template(navbar),

		initialize: function(options) {
		},
		
		events: {
		},
		
		render: function() {
			// render the view
			this.$el.html( this.navBarTemplate({login: dStore.userName}) );			
			return this;
		}
});

	return navbarView;
});
