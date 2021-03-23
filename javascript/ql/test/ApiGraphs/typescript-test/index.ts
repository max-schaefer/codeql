export interface Sized {
  getSize(): number;
}

import * as mongoose from "mongoose";
var myModel: mongoose.Model;

export type MyModel = mongoose.Model;

export enum AccessLevel {
  None,
  Read = 1 << 1,
  Write = 1 << 2,
  ReadWrite = Read | Write,
  Boss = "123".length,
};