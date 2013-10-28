define([
 'jquery'
 ,'backbone'
 ,'gapi'
 ,'moment'
 ,'collections/tasklists'
 ,'views/appView'
], 

function($, Backbone, ApiManager, moment, Tasks, AppView) {
	var App = function(ApiManager) {
		// global event dispatcher
		this.dispatcher = _.extend({}, Backbone.Events);
		this.collections.tasks = new Tasks();
		this.connectDropbox();	
		this.moment = moment;
	};

	App.prototype = {
		views: {},
		collections: {},
		variables: {},
		connectDropbox: function() {
			var that = this
			;
			
			this.apiManager = new ApiManager(this);
			
			that.apiManager.client.getAccountInfo(function(response, options) {
				that.userEmail = options.email;
				that.userName = options.name;
			});
			
			if (that.apiManager.dataStoreManager) {				
				that.apiManager.dataStoreManager.openDefaultDatastore(function (error, dataStore) {
					if (error) {
						console.dir('Error opening default datastore: ' + error);
					}
				
					// Now you have datastores. 
					that.dataStore = dataStore;
					
					dataStore.recordsChanged.addListener(function (event) {
						if (!event.isLocal()) { 
							var data, records = event.affectedRecordsForTable('tasks');
							var c = that.collections.tasks;
							var m = c.get(records[0].getId());
							
							if (m) {
								if	(records[0].isDeleted()) {
									m.trigger('removeView', m);
									m.clear({silent: true});
								} else
									m.set(records[0].getFields());
							} else {
								data = records[0].getFields();
								data.id = records[0].getId();
								c.add(data, {newTask: true});
								//console.dir(c)
							}
						}
					});
					
					that.views.appView = new AppView({collection: that.collections.tasks, dispatcher: that.dispatcher});
					
					that.collections.tasks.fetch({
						success: function(model, response) { 
							var container = that.views.appView.render().el;
							$('body')
								.hide()
								.html(container)
								.fadeIn(500);
						}
					});		
				});
			}
		}
	};

	return App;
});