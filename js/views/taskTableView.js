define([
  'text!templates/tasksTable.html'  
  , 'views/tasksView'

],

function(template, TasksView) {
  var TasksTableView = Backbone.View.extend({
    //tagName: 'tr',
    //className: 'list-menu-item',

    template: _.template(template),

	initialize: function(options) {
		this.dispatcher = options.dispatcher;
		//this.listenTo(this.model, 'destroy removeView', this.remove);
		//this.listenTo(this.model, 'change', this.render);
		this.listenTo(this.collection, 'add', this.newTask);
		//this.dispatcher.on('filterTable', this.filterTable, this);
		//this.dispatcher.on('clearFilter', this.render, this);
    },
		
    events: {
		'click .search' :  'searchTable'
		//, 'keyup .searchTerm' :  'searchTable'
    },
	
	bindings: {
	},
	
	archive: function(){
		var completed = this.collection.where({completed: true});
		_.each(completed, function(model) {
			model.archive();
		});
	},
	
	filterTable: function(term){
		//console.dir(term);
		var pattern = new RegExp(term,"gi");
	
		if (term.length > 1) {
			this.results = this.collection.filter(function(model){
				return pattern.test(model.get("taskname"));
			});
			this.filteredCollection = new Backbone.Collection(this.results);
			//console.dir(this.results);
			this.render();
		}
	},
	
	newTask: function(model, collection, options){
		var that = this, view;
		view = new TasksView({model: model, dispatcher: that.dispatcher});
		this.$el.find('tbody').append(view.render().el);
	},
		
    render: function(options) {
		var that = this
			, coll = this.collection
		;
		
		this.$el.html( this.template() );
		
		// render the sub-views
		coll.each(function(model) {
			trRow = new TasksView({ model: model, dispatcher: that.dispatcher });
			container.appendChild(trRow.render().el)
		});
		this.$el.find('tbody').append(container);

		return this;
    }
	
  });

  return TasksTableView;
});
