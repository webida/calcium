function foo() {
    var x;
    {
        var y;
        for (var z = 0; z < 10; z++) {}
    }
    return x + y + z;
}
