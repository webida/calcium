var fs = require('fs');
var infer = require('./infer.js');

// use first given parameter as input file
fs.readFile(process.argv[2], 'utf8', function (err, data) {
  if (err) {
	  return console.log(err);
	}
	infer.analyze(data);
});


