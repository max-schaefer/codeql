const lib = require('lib');
lib.callback((parm) => {
    var tainted = parm.f;
    var sanitized = lib.sanitize(tainted);
    lib.sink(sanitized);
})

// make sure we have enough occurrences of the representations we care about
lib.callback((parm) => parm.f);
lib.callback((parm) => parm.f);
lib.callback((parm) => parm.f);
lib.callback((parm) => parm.f);
