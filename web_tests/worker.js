importScripts('../dist/yatern.js');

addEventListener('message', function (e) {
    var t1 = (new Date).getTime();
    var gObject = YAtern.analyze(e.data.code);
    var t2 = (new Date).getTime();
    console.log("Time spent: " + (t2 - t1));

    var message = {};

    var typeNames = '';
    var propNames = '';

    var types = gObject.getProp('x').types;

    types.forEach(function (type) {
        typeNames += type.name + ', ';
        if (type.props) {
            type.props.forEach(function (value, key) {
                propNames += key + ', ';
            });
        }
    });
    message.typeNames = typeNames;
    message.propNames = propNames;

    postMessage(message);
});
