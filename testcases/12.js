// should stringfy number props
var obj = {1 : true, '2': 'two'};
var x1 = obj[1];
var x2 = obj['1'];
var x3 = obj[2];
var x4 = obj['2'];

// also for the indexes
var arr = ['', true];
var x5 = arr[1];
var x6 = arr['1'];
