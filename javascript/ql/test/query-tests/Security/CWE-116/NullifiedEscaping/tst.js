function nullifiedEscape(s) {
  s = s.replace(/\\/g, "\\\\").replace(/"/g, '\\"');
  return decodeURIComponent(s);
}

function clone(s) {
  return JSON.parse(JSON.stringify(s));
}
