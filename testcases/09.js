function Foo(data) {
    this.data = data; 
}  
Foo.prototype.getData = function (x) {      
    return this.data; 
};  
var foo = new Foo(''); 
var y = foo.getData();