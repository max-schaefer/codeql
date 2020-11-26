/**
 * Toy example based on Fib 2.a of Seldon paper, using imaginary `sanitize-path` package.
 *
 * Translated from Python to JavaScript, and adapted to use Express.
 */

const express = require('express');
const fs = require('fs');
const path = require('path');

const app = express();
const port = 3000;

app.use(express.json());

const appDir = process.env.APP_PATH;
console.log(`Using appDir=[${appDir}]`);

// Should report warning 
app.post('/unsanitized', (req, res) => {
    console.log(req.body);
    // line 12 Fig 2.a req.body.path is pretending `request.files['f'].filename` on paper
    var resolvedPath = path.join(appDir, req.body.path);
    // line 14 Fig 2.a req.body.contents is pretending request.files['f'] 
    fs.writeFile(resolvedPath, req.body.contents, (err) => {
        if (err) {
            res.sendStatus(500);
        } else {
            res.sendStatus(200);
        }
    });
});

// Should not report warning 
app.post('/sanitized', (req, res) => {
    console.log(req.body);
    // line 12 Fig 2.a req.body.path is pretending `request.files['f'].filename` on paper
    var resolvedPath = path.join(appDir, req.body.path);
    // line 13 Fig 2.a secure filename(filename)
    resolvedPath = require('sanitize-path')(resolvedPath);
    // line 14 Fig 2.a req.body.contents is pretending request.files['f']
    if (resolvedPath)
        fs.writeFile(resolvedPath, req.body.contents, (err) => {
            if (err) {
                res.sendStatus(500);
            } else {
                res.sendStatus(200);
            }
        });
});

app.listen(port, () => {
    console.log(`Application listening on port ${port}...`);
});

// make sure we have enough occurrences of the representations we care about
(function() {
    require('sanitize-path')();
    require('sanitize-path')();
    require('sanitize-path')();
    require('sanitize-path')();
    require('sanitize-path')();
})