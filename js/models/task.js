define(function() {
	var Task = Backbone.Model.extend({
		url: 'tasks',
		//defaults: { title: '', notes: '' }
		parse: function	 (resp) {
			return resp;
		}
		, toDropbox: function() {
			var attrs = _.clone(this.attributes);
			delete attrs.id;
			return attrs;
		}
		, toggle: function() {
			this.save({completed: !this.get("completed")});
		}
	});

	return Task;
});