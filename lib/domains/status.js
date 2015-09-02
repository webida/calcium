// Status:
// { self  : AVal,
//   ret   : AVal,
//   exc   : AVal,
//   delta : Context,
//   sc    : Scope }

export class Status {
    constructor(self, ret, exc, delta, sc) {
        this.self = self;
        this.ret = ret;
        this.exc = exc;
        this.delta = delta;
        this.sc = sc;
    }

    equals(other) {
        return this.self === other.self &&
            this.ret === other.ret &&
            this.exc === other.exc &&
            this.delta === other.delta &&
            this.sc === other.sc;
    }

    getNewStatus(changeStatus) {
        const newStatus = new Status;
        for (let p in this) {
            if (this.hasOwnProperty(p)) {
                if (changeStatus.hasOwnProperty(p)) {
                    newStatus[p] = changeStatus[p];
                } else {
                    newStatus[p] = this[p];
                }
            }
        }
        return newStatus;
    }
}
