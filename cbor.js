/*
 * The MIT License (MIT)
 *
 * Copyright (c) 2014-2016 Patrick Gansterer <paroga@paroga.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

const POW_2_24 = 5.960464477539063e-8;
const POW_2_32 = 4294967296;
const POW_2_53 = 9007199254740992;

const utf8Decoder = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });

// Decodes exactly one CBOR item from an ArrayBuffer. Throws a RangeError when
// the input is truncated, and an Error for any other malformed input.
export function decode(data) {
  const dataView = new DataView(data);
  let offset = 0;

  function commitRead(length, value) {
    offset += length;
    return value;
  }
  function readBytes(length) {
    return commitRead(length, new Uint8Array(data, offset, length));
  }
  function readFloat16() {
    const value = readUint16();
    const sign = value & 0x8000;
    let exponent = value & 0x7c00;
    const fraction = value & 0x03ff;

    if (exponent === 0x7c00)
      exponent = 0xff << 10;
    else if (exponent !== 0)
      exponent += (127 - 15) << 10;
    else if (fraction !== 0)
      return (sign ? -1 : 1) * fraction * POW_2_24;

    const tempDataView = new DataView(new ArrayBuffer(4));
    tempDataView.setUint32(0, sign << 16 | exponent << 13 | fraction << 13);
    return tempDataView.getFloat32(0);
  }
  const readFloat32 = () => commitRead(4, dataView.getFloat32(offset));
  const readFloat64 = () => commitRead(8, dataView.getFloat64(offset));
  const readUint8 = () => commitRead(1, dataView.getUint8(offset));
  const readUint16 = () => commitRead(2, dataView.getUint16(offset));
  const readUint32 = () => commitRead(4, dataView.getUint32(offset));
  function readUint64() {
    const high = readUint32();
    if (high >= POW_2_53 / POW_2_32)
      throw new Error("Integer too large to represent exactly");
    return high * POW_2_32 + readUint32();
  }
  function readBreak() {
    if (dataView.getUint8(offset) !== 0xff)
      return false;
    offset += 1;
    return true;
  }
  function readLength(additionalInformation) {
    if (additionalInformation < 24)
      return additionalInformation;
    switch (additionalInformation) {
      case 24: return readUint8();
      case 25: return readUint16();
      case 26: return readUint32();
      case 27: return readUint64();
      case 31: return -1;
    }
    throw new Error("Invalid length encoding");
  }
  function readIndefiniteStringLength(majorType) {
    const initialByte = readUint8();
    if (initialByte === 0xff)
      return -1;
    const length = readLength(initialByte & 0x1f);
    if (length < 0 || (initialByte >> 5) !== majorType)
      throw new Error("Invalid indefinite length element");
    return length;
  }
  const readUtf8String = length => utf8Decoder.decode(readBytes(length));

  function readMap(length) {
    const map = {};
    for (let i = 0; i < length || (length < 0 && !readBreak()); ++i) {
      const key = decodeItem();
      if (Object.hasOwn(map, key))
        throw new Error("Duplicate map key: " + key);
      // Plain assignment would let a "__proto__" key replace the prototype.
      Object.defineProperty(map, key, {
        value: decodeItem(),
        writable: true,
        enumerable: true,
        configurable: true
      });
    }
    return map;
  }

  function decodeItem() {
    const initialByte = readUint8();
    const majorType = initialByte >> 5;
    const additionalInformation = initialByte & 0x1f;

    if (majorType === 7) {
      switch (additionalInformation) {
        case 25: return readFloat16();
        case 26: return readFloat32();
        case 27: return readFloat64();
      }
    }

    let length = readLength(additionalInformation);
    if (length < 0 && (majorType < 2 || 5 < majorType))
      throw new Error("Invalid length");

    switch (majorType) {
      case 0:
        return length;
      case 1:
        return -1 - length;
      case 2: {
        if (length >= 0)
          return readBytes(length);
        const chunks = [];
        while ((length = readIndefiniteStringLength(majorType)) >= 0)
          chunks.push(readBytes(length));
        const bytes = new Uint8Array(chunks.reduce((sum, chunk) => sum + chunk.length, 0));
        let bytesOffset = 0;
        for (const chunk of chunks) {
          bytes.set(chunk, bytesOffset);
          bytesOffset += chunk.length;
        }
        return bytes;
      }
      case 3: {
        if (length >= 0)
          return readUtf8String(length);
        const chunks = [];
        while ((length = readIndefiniteStringLength(majorType)) >= 0)
          chunks.push(readUtf8String(length));
        return chunks.join("");
      }
      case 4: {
        const array = [];
        if (length < 0) {
          while (!readBreak())
            array.push(decodeItem());
        } else {
          for (let i = 0; i < length; ++i)
            array.push(decodeItem());
        }
        return array;
      }
      case 5:
        return readMap(length);
      case 6:
        // Tags are not interpreted; return the tagged item itself.
        return decodeItem();
      case 7:
        switch (length) {
          case 20: return false;
          case 21: return true;
          case 22: return null;
          default: return undefined;
        }
    }
  }

  const ret = decodeItem();
  if (offset !== data.byteLength)
    throw new Error("Remaining bytes");
  return ret;
}
