var fs = require('fs');
var infer = require('./infer.js');

// use first given parameter as input file
fs.readFile(process.argv[2], 'utf8', function (err, data) {
    if (err) {
        console.log(err);
        return;
    }
    infer.analyze(data);
});


