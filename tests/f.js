var e = 1;

try {
	throw 0;
} catch (e) {
	var f = function (x) {
		function g() {
			console.log(e);
			console.log(x);
		}
		console.log(e);
		g();
	};
	f(2);
}

