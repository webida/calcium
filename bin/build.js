var fs = require('fs'), path = require('path');
var stream = require('stream');

var browserify = require('browserify');
var babelify = require('babelify').configure({loose: 'all'});

process.chdir(path.resolve(__dirname, '..'));

// make ./dist if not exist
if (!fs.existsSync('dist')) {
    fs.mkdirSync('dist');
}

// build for web
browserify({standalone: 'calcium', debug: true})
    .transform(babelify)
    .require('./lib/infer.js', {entry: true})
    .bundle()
    .on('error', function (err) { console.log('Error: ' + err.message) })
    .pipe(fs.createWriteStream('dist/calcium.js'));
