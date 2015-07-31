importScripts('../dist/yatern.js');

addEventListener('message', function (e) {
    var t1 = (new Date()).getTime();
    try {
        var result = YAtern.analyze(e.data.code, true);
    } catch (e) {
        // analysis fail
        return {};
    }
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

    var varAtPos = YAtern.findIdentifierAt(result.AST, e.data.pos);
    if (varAtPos) {
        message.varNameAtPos = varAtPos.node.name;
        console.log(varAtPos.state);

        var refs = YAtern.findVarRefsAt(result.AST, e.data.pos);
        message.varOccurrences = refs;


    } else {
        message.varNameAtPos = null;
    }

    var onFunctionOrReturnKeyword = YAtern.onFunctionOrReturnKeyword(result.AST, e.data.pos);

    if (onFunctionOrReturnKeyword) {
        message.returnList = YAtern.findReturnStatements(result.AST, e.data.pos);
    }

    var onThisKeyword = YAtern.onThisKeyword(result.AST, e.data.pos);

    if (onThisKeyword) {
        message.thisList = YAtern.findThisExpressions(result.AST, e.data.pos, true);
    }

    message.typeNames = typeNames;
    message.propNames = propNames;
    message.onFunctionOrReturnKeyword = onFunctionOrReturnKeyword;
    message.onThisKeyword = onThisKeyword;

    postMessage(message);
});
