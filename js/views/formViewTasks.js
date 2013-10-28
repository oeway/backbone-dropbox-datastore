define([
  'text!templates/tasksForm.html',
  'models/task'
],

function(template, Task) {
  var FormViewTasks = Backbone.View.extend({
    //tagName: 'form',
	
    template: _.template(template),

	initialize: function(options) {
		this.files = options.files;
		this.dispatcher = options.dispatcher;
		this.dispatcher.on('updateForm', this.updateForm, this);
		//this.dispatcher.on('toggleForm', this.slideToggle, this );
    },
	
    events: {
		'click button[type=submit]' : 'submit'
		, 'click .closeForm'		: 'closeForm'
    },
	
	bindings: {
		'.taskid': {
			observe: 'id'
		},
		'.taskname': {
			observe: 'taskname',
			updateModel: false
		}
	},
		
	updateForm: function(model) {
		this.model = model;
		this.stickit();
		if ( !this.$el.is(":visible") ) {
			this.$el.slideDown();
		}		
	},
	
	closeForm: function(e) {
		var that = this;
		e.preventDefault();
		if ( that.$el.is(":visible") ) {
			that.$el.slideToggle(function(){
				that.dispatcher.trigger('toggleFormButton');
			});
		}
		that.newTask();		
	},
	
	slideToggle: function(e) {
		//console.dir(this);
		if ( !this.$el.is(":visible") )
			this.$el.slideToggle();
		this.newTask();
	},
	
	// submit the form
	submit: function(e){
		e.preventDefault();
		var that = this
		;
		
		m = that.model.set(this.$el.serializeForm(), {validate: true});
		if (m) {
			m.save({created: new Date(), completed: false});
			this.newTask();
		}

	},
	
	newTask: function() {
		this.$el.find('#inputTask').focus();
		$('#addTasksForm').find('input:text, input:password, input:file, input:hidden, select, textarea').val('');
		this.model = new Task();
	},
	
    render: function() {
		var that = this
		;
		this.$el.html( this.template( ) );
		that.stickit();
				
		return this;
    }
});

  return FormViewTasks;
});
