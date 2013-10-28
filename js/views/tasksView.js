define([
  'text!templates/tasksTr.html'
],

function(template) {
  var TasksView = Backbone.View.extend({
    tagName: 'tr',
    //className: 'list-menu-item',

    template: _.template(template),

	initialize: function(options) {
		this.dispatcher = options.dispatcher;
		this.listenTo(this.model, 'destroy removeView', this.remove);
		this.listenTo(this.model, 'change', this.render);
		this.listenTo(this.model, 'change:archive', this.archive);
		
		//console.dir(this.model);
    },
		
    events: {
		'click .btn-edit-task'		: 'editTask',
		'click .btn-del-task'		: 'delTask',
		'click .isCompleted'		: 'toggleDone'
    },
	
	bindings: {
		'.task_name': {
			observe: 'taskname',
			updateModel: false
		},
		'.task_date': {
			observe: 'created'
			, onGet: 'format_created_date'
		},
		'.isCompleted': {
			observe: 'completed'
			, updateModel: false
		},
		'.task_ref': {
			observe: 'tasksFileRef'
			, onGet: function(value, options) {
				return value;
			},
			updateModel: false,
			afterUpdate: function($el, val, options) {
				$el.fadeOut(500, function() { $(this).fadeIn(500); });
			}
		},
		/*'.task_no': {
		  observe: 'id'
		}*/
		'.task_no': {
			observe: 'id',
			update: function($el, val, model, options) { $el.text(model.collection.indexOf(model)+1); }
		}
	},
		
	toggleDone: function() {
		this.model.toggle();
    },
	
	archive: function() {
		this.remove();
		this.model.collection.remove(this.model, {silent: true});
	},
		
	format_created_date: function(value, options) {
		var r;
		r = value ? dStore.moment(value).format("ddd, D MMMM @ h:mm a") : "";
		return r;
	},
	
	editTask: function(e) {
		e.preventDefault();
		//console.dir(this);
		document.getElementById('inputTask').focus();
		this.dispatcher.trigger('updateForm', this.model );
		this.dispatcher.trigger('toggleFormButton');
	},	
	
	delTask: function(e) {
		e.preventDefault();
		this.model.destroy();		
	},	
	
    render: function() {
		var that = this
		;
		this.$el.html( this.template( this.model.toJSON() ) );
		this.$el.children().not('.noStrikethrough').toggleClass('completed', this.model.get('completed'));
		that.stickit();
	
		return this;
    }
	
  });

  return TasksView;
});
