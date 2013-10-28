define([
  'text!templates/scaffold.html'
, 'views/taskTableView'
, 'views/formViewTasks'
, 'views/navbarView'
, 'models/task'
],

function(template, TasksTableView, FormViewTasks, NavbarView, Task) {
	var AppView = Backbone.View.extend({  // change the name here
		tagName: 'div',
		className: 'container',

		template: _.template(template),

		initialize: function(options) {
			this.navbarView = new NavbarView();
			this.dispatcher = options.dispatcher;
			this.form = document.getElementById('addTasksForm');
			this.dispatcher.on('toggleFormButton', this.toggleFormButton, this);
			this.listenTo(this.collection, 'add remove', this.stats, this);
		},
		
		events: {
			'click #showFormButton'	: 'toggleForm'
		},
		
		stats: function() {
			var el = document.getElementsByClassName('countTasks')[0];
			if (el) el.innerHTML = this.collection.length;
		},
		
		toggleForm: function(e) {
			$(e.currentTarget).hide();
			this.dispatcher.trigger('updateForm', new Task() );
		},
	
		
		toggleFormButton: function() {
			var form = document.getElementById('addTasksForm')
				, btn = document.getElementById('showFormButton');
			
			if ( $(form).is(":visible") )
				$(btn).hide(); 
			else 
				$(btn).show();
		},
		
		render: function() {
			var that = this
				container = document.createDocumentFragment()
			;		
			
			// render the main view
			this.$el.html( this.template() );
			
			// render the sub-views
			this.navbarView.setElement(this.$('.navbar')).render();
			new FormViewTasks({model: new Task(), dispatcher: that.dispatcher }).setElement(this.$('.formView')).render();
			new TasksTableView({collection: that.collection, dispatcher: that.dispatcher }).setElement(this.$('.tableView')).render();
			
			_.defer(function() {
				that.toggleFormButton();
				that.stats();
			});
			
			return this;
		}	
	});

	return AppView;
});
