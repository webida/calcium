var x, y;

function f() {
    x = 3;
}

function Foo(data) {
    this.data = data;
}

Foo.prototype.getData = function () {
    y = this.data;
    return this.data;
};

var foo = new Foo('');

