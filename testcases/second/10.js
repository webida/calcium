function Foo(data) {
    this.data = data;
}
Foo.prototype.getData = function () {
    return this.data;
};
Foo.prototype.empty = null;

var foo = new Foo('Hello');
var x = foo.;
