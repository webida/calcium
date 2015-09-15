var arr = [];
// Propagate PrimNumber to unknown prop of arr
arr[0+0] = 3;
arr['a'] = '';
// Use unknown property
// since abstract property '0' of arr does not exist.
var x = arr[0];

var arr2 = {};
// We do not assign to unknown for usual property.
arr2.a = 3;
var y = arr2.b;
