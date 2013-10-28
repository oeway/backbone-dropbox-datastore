define([
  'text!templates/scaffold.html'
, 'views/tasksView'
, 'views/formView'
, 'models/task'
],

function(template, TasksView, FormView, Task) {
	var AppView = Backbone.View.extend({  // change the name here
		tagName: 'div',
		className: 'container',

		template: _.template(template),

		initialize: function() {
			this.formView = new FormView({model: new Task() });
		},
		
		events: {
		
		},
		
		render: function() {
			var that = this
			container = document.createDocumentFragment()
			;		
			
			// render the main view
			this.$el.html( this.template() );
			
			// render the form sub-view
			this.formView.setElement(this.$('.taskForm')).render();
			
			// render the sub-views
			that.collection.each(function(model) {
				trRow = new TasksView({ model: model });
				container.appendChild(trRow.render().el)
			});
			this.$el.find('tbody').append(container);
					
			return this;
		}
	
	});

	return AppView;
});
