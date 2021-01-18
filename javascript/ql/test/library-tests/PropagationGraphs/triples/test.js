const lib = require('lib');
var tainted = lib.source();
var sanitized = lib.sanitize(tainted);
lib.sink(sanitized);
lib.sink2({ prop: sanitized });

// make sure we have enough occurrences of the representations we care about
lib.source();
lib.source();
lib.source();
lib.source();
lib.sanitize(tainted);
lib.sanitize(tainted);
lib.sanitize(tainted);
lib.sanitize(tainted);
lib.sink({});
lib.sink({});
lib.sink({});
lib.sink({});
lib.sink2({ prop: {} });
lib.sink2({ prop: {} });
lib.sink2({ prop: {} });
lib.sink2({ prop: {} });
