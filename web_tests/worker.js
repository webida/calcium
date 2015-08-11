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

    var varAtPos = YAtern.findIdentifierAt(result.AST, e.data.end);
    if (varAtPos) {
        message.varNameAtPos = varAtPos.node.name;
        console.log(varAtPos.state);

        var refs = YAtern.findVarRefsAt(result.AST, e.data.end);
        message.varOccurrences = refs;


    } else {
        message.varNameAtPos = null;
    }

    var onFunctionOrReturnKeyword = YAtern.onFunctionOrReturnKeyword(result.AST, e.data.end);

    if (onFunctionOrReturnKeyword) {
        message.returnList = YAtern.findReturnStatements(result.AST, e.data.end);
    }

    var onThisKeyword = YAtern.onThisKeyword(result.AST, e.data.end);

    if (onThisKeyword) {
        message.thisList = YAtern.findThisExpressions(result.AST, e.data.end, true);
    }

    var typeData = YAtern.getTypeData(result.AST, result.Ĉ, e.data.start, e.data.end);

    message.typeNames = typeNames;
    message.propNames = propNames;
    message.onFunctionOrReturnKeyword = onFunctionOrReturnKeyword;
    message.onThisKeyword = onThisKeyword;
    message.typeData = typeData;

    postMessage(message);
});
