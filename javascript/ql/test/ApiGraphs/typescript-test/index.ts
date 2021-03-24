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

export class Point {
  x: number;
  y: number;

  distanceFrom(point: Point) {
    return Math.sqrt((this.x - point.x) ** 2 + (this.y - point.y) ** 2);
  }
}
