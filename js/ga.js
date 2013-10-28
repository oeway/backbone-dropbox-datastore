define([], function() {
	var registerGoogleAnalytics = function(accountId) {
		var _gaq = _gaq || [];
		if (window) {
			window._gaq = _gaq; // export as global
		}
		_gaq.push(['_setAccount', accountId]);
		_gaq.push(['_trackPageview']);
	 
		(function(d,t){var g=d.createElement(t),s=d.getElementsByTagName(t)[0];
		g.src='//www.google-analytics.com/ga.js';
		s.parentNode.insertBefore(g,s)}(document,'script'));
	}

	return registerGoogleAnalytics;
});