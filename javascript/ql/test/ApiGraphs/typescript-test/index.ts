export interface Sized {
  getSize(): number;
}

import * as mongoose from "mongoose";
var myModel : mongoose.Model;

export type MyModel = mongoose.Model;