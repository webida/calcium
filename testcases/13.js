// '<i>' was the internal property for unknown props
var obj = {'<i>' : true};
obj[1+1] = 1;
var x = obj['<i>'];
var y = obj[1+2];

function f(x) {
    return arguments;
}

var z = f(1)[0];