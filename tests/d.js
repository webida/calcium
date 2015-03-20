var e = 1;
try {
	throw 0;
} catch (e) {
	function f() {
		// function decl escapes catch scope
		console.log(e); // output 1
	}
	f();  

	console.log(e); // output 0

	var g = function () {
		console.log(e); // output 0
	};
	g();
}


// g cannot see the catch parameter 'e'
// catch parameter does not shadow f' e from g's access
