importScripts('../dist/yatern.js');

addEventListener('message', function (e) {
    var t1 = (new Date()).getTime();
    var result = YAtern.analyze(e.data.code, true);
    var gObject = result.gObject;
    var t2 = (new Date()).getTime();
    console.log('Time spent: ' + (t2 - t1));

    var message = {};

    var typeNames = '';
    var propNames = '';

    // find types
    var types = gObject.getProp('x').types;

    // find object prop names
    types.forEach(function (type) {
        typeNames += type.name + ', ';
        if (type.props) {
            type.props.forEach(function (value, key) {
                propNames += key + ', ';
            });
        }
    });

    var varNodeAtPos = YAtern.findIdentifierNodeAt(result.AST, e.data.pos);
    if (varNodeAtPos) {
        message.varNameAtPos = varNodeAtPos.name;
    } else {
        message.varNameAtPos = null;
    }

    message.typeNames = typeNames;
    message.propNames = propNames;

    message.varOccurrences = [{start: 0, end: 1}, {start: 3, end: 4}];

    postMessage(message);
});
