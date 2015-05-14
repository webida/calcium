var types = require('../domains/types');
var status = require('../domains/status');
var cGen = require('./cGen');

function CSTR() {}
CSTR.prototype = Object.create(null);
CSTR.prototype.equals = function (other) {
    return this === other;
};

function ReadProp(prop, to) {
    this.prop = prop;
    this.to = to;
}
ReadProp.prototype = new CSTR;
ReadProp.prototype.addType = function (obj) {
    if (!(obj instanceof (types.ObjType))) return;
    // when obj is ObjType,
    var ownProp = obj.getProp(this.prop, true);
    if (ownProp) {
        // when the object has the prop,
        ownProp.propagate(this.to);
    } else if (obj.getProp('__proto__', true)) {
        // use prototype chain
        obj.getProp('__proto__')
          .propagate(new ReadProp(this.prop, this.to));
    }
};
ReadProp.prototype.equals = function (other) {
    if (!(other instanceof ReadProp)) return false;
    return this.prop === other.prop
        && this.to.equals(other.to);
};

function WriteProp(prop, from) {
    this.prop = prop;
    this.from = from;
}
WriteProp.prototype = new CSTR;
WriteProp.prototype.addType = function (obj) {
    if (!(obj instanceof (types.ObjType))) return;
    var ownProp = obj.getProp(this.prop);
    this.from.propagate(ownProp);
};

function IsAdded(other, target) {
    this.other = other;
    this.target = target;
}
IsAdded.prototype = new CSTR;
IsAdded.prototype.addType = function (type) {
    if (type === types.PrimNumber
     && this.other.hasType(types.PrimNumber)) {
        this.target.addType(types.PrimNumber);
    }
    if (type === types.PrimString
     && !this.other.isEmpty()) {
         this.target.addType(types.PrimString);
    }
};

function IsCallee(self, args, ret, exc, delta) {
    this.self = self;
    this.args = args;
    this.ret = ret;
    this.exc = exc;
    this.delta = delta;
}
IsCallee.prototype = new CSTR;
IsCallee.prototype.addType = function (f) {
    if (!(f instanceof (types.FnType))) return;
    var funEnv = f.getFunEnv(this.delta);
    var newSC = f.originNode.body['@block'].getScopeInstance(f.sc, this.delta);
    var funStatus 
        = new status.Status(funEnv[0], funEnv[1], funEnv[2], 
                            this.delta, newSC);
    // pass this object
    this.self.propagate(funEnv[0]);

    // propagate arguments
    for (var i = 0; i < this.args.length; i++) {
        this.args[i].propagate(newSC.getAValOf(f.paramNames[i]));
    }

    // constraint generation for the function body
    cGen.addConstraints(f.originNode.body, funStatus);
    
    // get return 
    funEnv[1].propagate(this.ret);
    // get exception
    funEnv[2].propagate(this.exc);
};

exports.ReadProp = ReadProp;
exports.WriteProp = WriteProp;
exports.IsAdded = IsAdded;
exports.IsCallee = IsCallee;