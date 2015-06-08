importScripts('../dist/yatern.js');

addEventListener('message', function (e) {
    var data = e.data;
    //console.log(e.data.code);
    var t1 = (new Date).getTime();
    var gObject = YAtern.analyze(e.data.code);
    var t2 = (new Date).getTime();
    console.log("Time spent: " + (t2 - t1));

    var message = {};

    var typeNames = '';
    var propNames = '';

    var types = gObject.getProp('x').types;
    for (var i = 0; i < types.length; i++) {
        typeNames += types[i].name + '\n';
        if (types[i].props) {
            propNames += Object.getOwnPropertyNames(types[i].props) + '\n';
        }
    }
    message.typeNames = typeNames;
    message.propNames = propNames;

    postMessage(message);
});
