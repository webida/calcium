// context-sensitively analyze 'id' function
function id(x) { return x; }
var x = id(1);
var y = id(true);

// context-insensitively analyze 'foo' function
function foo(y) { return y; }
var a = foo(1);
var b = foo(true);
