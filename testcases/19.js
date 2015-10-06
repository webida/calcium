var x, y, z;

function f() {
    x = 3;
}

var g = function () {
    y = false;
};

function Foo(data) {
    this.data = data;
}

Foo.prototype.getData = function () {
    z = this.data;
    return this.data;
};

var foo = new Foo('');

