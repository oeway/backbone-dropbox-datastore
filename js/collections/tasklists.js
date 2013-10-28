define(['models/task'], function(Task) {
	
	var TaskLists = Backbone.Collection.extend({
		model: Task
		, url: 'tasks'
	});

	return TaskLists;
});