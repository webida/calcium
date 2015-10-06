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

    var start = e.data.start, end = e.data.end;
    var message = {};

    var typeNames = '';
    var propNames = '';

    // find id or member node
    YAtern.getCompletionAtPos(result, end);

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

    var varAtPos = YAtern.findIdentifierAt(result.AST, end);
    if (varAtPos) {
        message.varNameAtPos = varAtPos.node.name;
        console.log(varAtPos.state);

        var refs = YAtern.findVarRefsAt(result.AST, end);
        message.varOccurrences = refs;


    } else {
        message.varNameAtPos = null;
    }

    var onFunctionOrReturnKeyword = YAtern.onEscapingStatement(result.AST, end);

    if (onFunctionOrReturnKeyword) {
        message.escapingList = YAtern.findEscapingStatements(result.AST, end, true);
    }

    var onThisKeyword = YAtern.onThisKeyword(result.AST, end);

    if (onThisKeyword) {
        message.thisList = YAtern.findThisExpressions(result.AST, end, true);
    }

    var typeData = YAtern.getTypeData(result.AST, result.Ĉ, start, end);

    message.typeNames = typeNames;
    message.propNames = propNames;
    message.onEscapingStatement = !!onFunctionOrReturnKeyword;
    message.onThisKeyword = !!onThisKeyword;
    message.typeData = typeData;

    postMessage(message);
});
