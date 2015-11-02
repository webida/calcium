var obj = {aa: {cc: ''}, bb: false, ab: ''};

function Foo(data) {
    this.data = data;
}
Foo.prototype.getData = function () {
    return this.data;
};

var foo = new Foo('Hello');
var data = foo.getData();

var arr = [1, false, ''];
var elt = arr[0];
