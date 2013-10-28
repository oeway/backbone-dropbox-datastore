define(['config'], function(config) {
	var app
	, client = new Dropbox.Client({key: config.apiKey});

	function ApiManager(_app) {
		var app = _app;
		this.dropboxAuth(app);
	}

	ApiManager.prototype.dropboxAuth = function(app) {
		client.authenticate();
		
		if ( client.isAuthenticated() ) {
			this.dataStoreManager = client.getDatastoreManager();
			this.client = client;
		}
	};
	
	Backbone.sync = function(method, model, options) {
		
		var request
		, response
		, table
		, record
		, result
		;

		options = options || {};
		
		switch(method) {	
			case 'read':
				request = dStore.dataStore.getTable(model.url);	
				response = request.query();
				Backbone.gapiRequest(response, method, model, options);
			break;
			
			case 'create':
				table = dStore.dataStore.getTable(model.url);	
				response = table.insert(model.toDropbox());
				record = response.getFields();
				record.id = response.getId();
				options.success(record);
				dStore.collections[model.url].add(record);  // instead of bFiles -- app???
			break;
			
			case 'update':
				table = dStore.dataStore.getTable(model.url);
				record = table.get(model.id);
				//delete model.id // ???
				//console.dir(model.toDropbox());
				record.update(model.toDropbox());
				options.success(model.toJSON());
			break;
			
			case 'delete':
				table = dStore.dataStore.getTable(model.url);
				record = table.get(model.id);
				record.deleteRecord();
				options.success(model);
			break;
		}
		
	};
	
	Backbone.gapiRequest = function(response, method, model, options) {
		var record, rec
		//, data = new Array()
		, data = []
		;
		
		for (var i = 0; i < response.length; i++) {
			record = response[i];
			rec = record.getFields();
			rec.id = record.getId();
			data.push(rec);
		}
		options.success(data);
	};
	
	return ApiManager;
});
