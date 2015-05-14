var aux = require('../aux');

// for DEBUG
var count = 0;
// the abstract values for concrete values
// which are the sets of types
// We maintain 'props' for performance.
function AVal(type) {
    if (type) this.types = [type];
    else this.types = [];
    // to propagate
    this.forward = [];
    // OPTIONAL
    // for abstract values,
    // a prop is the merged AVals each types.
    //this.props = Object.create(null);
    // for DEBUG
    this._id = count++;
}

AVal.prototype.isEmpty = function () {
    return this.types.length === 0;
};

/**
 * @returns {[Type]}
 */
AVal.prototype.getTypes = function () {
    return this.types;
};

/**
 * @returns {boolean}
 */
AVal.prototype.hasType = function (type) {
    return this.types.indexOf(type) > -1;
};

/**
 * @param {Type} type
 */
AVal.prototype.addType = function (type) {
    if (this.types.indexOf(type) !== -1) return;
    // new type is added
    this.types.push(type);
    this.forward.forEach(function (fwd) {
       fwd.addType(type);
    });
};

AVal.prototype.propagate = function (target) {
    if (!this.addForward(target)) return;
    // target is newly added
    this.types.forEach(function (type) {
        target.addType(type);
    });
};

AVal.prototype.addForward = function (fwd) {
    for (var i = 0; i < this.forward.length; i++) {
        // equality is checked using equals methods.
        if (fwd.equals(this.forward[i])) return false;
    }
    this.forward.push(fwd);
    return true;
};

AVal.prototype.equals = function (other) {
    // simple reference comparison
    return this === other;
};

/**
 * @param {string} prop
 * @returns {AVal}
 */
AVal.prototype.getProp = function (prop) {
    if (prop === '✖') {
        // ✖ is the bogus property name added for error recovery.
        return AValNull;
    }
    var inProp = aux.internalName(prop);
    if (inProp in this.props) {
        // Assume AVal has the merged AVal for the prop.
        return this.props[inProp];
    } else {
        return AValNull;
    }
};

// super class of all types
// I assume that each type is distinguishable by '===' operation.
function Type() {}
Type.prototype = Object.create(null);
var AllType = new Type;

// 1. object types
/**
 * @param {AVal} proto - AVal of prototype object
 * @param {string} name
 */
function ObjType(proto, name) {
    this.name = name;
    this.props = Object.create(null);
    // make __proto__ property
    // this.joinAValToProp(proto, '__proto__');

    // share proto with __proto__
    this.setProp('__proto__', proto);
}
ObjType.prototype = Object.create(AllType);
/**
 * @param {string} prop
 * @returns {AVal} AVal of the property
 */
ObjType.prototype.getProp = function (prop, readOnly) {
    if (prop === '✖') {
        // ✖ is the bogus property name added during parsing error recovery.
        return AValNull;
    }
    var inProp = aux.internalName(prop);
    if (inProp in this.props) {
        return this.props[inProp];
    } else if (readOnly) {
        return null;
    } else {
        var newPropAVal = new AVal;
        this.props[inProp] = newPropAVal;
        return newPropAVal;
    }
};
/**
 * @param {string} prop
 * @param {AVal} aval
 */
ObjType.prototype.setProp = function (prop, aval) {
    if (prop === '✖') {
        // ✖ is the bogus property name added during parsing error recovery.
        return;
    }
    var inProp = aux.internalName(prop);
    this.props[inProp] = aval;
};
/**
 * @param {string} prop
 * @returns {boolean}
 */
ObjType.prototype.hasProp = function (prop) {
    if (prop === '✖') 
        return AValNull;
    var inProp = aux.internalName(prop);
    return (inProp in this.props);
};
/**
 * @param {Type} type
 * @param {string} prop
 */
ObjType.prototype.addTypeToProp = function (type, prop) {
    if (prop === '✖') return;
    var inProp = aux.internalName(prop);
    if (!this.props[inProp]) {
        this.props[inProp] = new AVal;
    }
    if (this.props[inProp].hasType(type)) return;
    this.props[inProp].addType(type);
};
/**
 * @param {AVal} aval
 * @param {string} prop
 */
ObjType.prototype.joinAValToProp = function (aval, prop) {
    var self = this;
    aval.getTypes().forEach(function (type) {
        self.addTypeToProp(type, prop);
    });
};

var AllObjType = new ObjType(new AVal, '[AllObjType]');

// make an Obj from the global scope
function mkObjFromGlobalScope(gScope) {
    var gObj = new ObjType(AValNull, "*global scope*");
    gObj.props = gScope.varMap;
    return gObj;    
}


// 2. primitive types
function PrimType(name) {
    this.name = name;
}
PrimType.prototype = Object.create(AllType);

// 3. function types
// the name is used for the type of the instances from the function
function FnType(fn_proto, name, argNames, sc, originNode) {
    ObjType.call(this, fn_proto, name);
    // this.thisAVal = new AVal;
    this.paramNames = argNames;
    // this.retAVal = new AVal;
    this.sc = sc;
    // body node of the function
    this.originNode = originNode;
    // funEnv : CallContext -> [self, ret, exc]
    this.funEnv = Object.create(null);
    // AVals for function usage
    // this.usage = Object.create(null);
}
FnType.prototype = Object.create(AllObjType);

// construct Status for function
FnType.prototype.getFunEnv = function(delta) {
    var instance = this.funEnv[delta]
        || (this.funEnv[delta] = [new AVal, new AVal, new AVal]);
    return instance;
};

// returns AVals for given function usage
FnType.prototype.getUsageAVals = function (delta) {
    if (this.usage[delta] === undefined) {
        var params = [];
        // for 'this'
        params.push(new AVal);
        // for regular parameters
        for (var i = 1; i < this.paramNames.length; i++) {
            params.push(new AVal);
        }
        return this.usage[delta] = {params: params, ret: new AVal, exc: new AVal};
    } else return this.usage[delta];
};

// 4. array types
function ArrType(arr_proto) {
    ObjType.call(this, arr_proto, 'Array');
}
ArrType.prototype = Object.create(AllObjType);

// Make primitive types
var PrimNumber = new PrimType('number');
var PrimString = new PrimType('string');
var PrimBoolean = new PrimType('boolean');

// AbsNull represents all empty abstract values.
var AValNull = new AVal();
// You should not add any properties to it.
AValNull.props = null;
// Adding types are ignored.
AValNull.addType = function () {};




// export
exports.Type = Type;
exports.ObjType = ObjType;
exports.FnType = FnType;
exports.ArrType = ArrType;
exports.PrimNumber = PrimNumber;
exports.PrimString = PrimString;
exports.PrimBoolean = PrimBoolean;
exports.mkObjFromGlobalScope = mkObjFromGlobalScope;

exports.AVal = AVal;
exports.AValNull = AValNull;