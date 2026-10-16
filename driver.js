/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this file,
 * You can obtain one at http://mozilla.org/MPL/2.0/. */

import * as CBOR from "./cbor.js";
import { Certificate, fromBER } from "./assets/pkijs.js";

const flag_TUP = 0x01;
const flag_AT = 0x40;
const flag_ED = 0x80;

const cose_kty = 1;
const cose_kty_ec2 = 2;
const cose_alg = 3;
const cose_alg_ECDSA_w_SHA256 = -7;
const cose_crv = -1;
const cose_crv_P256 = 1;
const cose_crv_x = -2;
const cose_crv_y = -3;

const $ = id => document.getElementById(id);

class ResultTracker {
  failures = 0;
  todos = 0;

  reset() {
    this.failures = 0;
    this.todos = 0;
  }
  fail() {
    this.failures += 1;
  }
  todo() {
    this.todos += 1;
  }
  toString() {
    return `Failures: ${this.failures} TODOs: ${this.todos}`;
  }
}

const gResults = new ResultTracker();

function append(id, text) {
  $(id).textContent += text;
}

function test(id, passed, text) {
  if (!passed) {
    gResults.fail();
  }
  append(id, `${passed ? "[PASS]" : "[FAIL]"} ${text}\n`);
  return passed;
}

function testEqual(id, val1, val2, msg) {
  const result = (val1 == val2);
  return test(id, result, `${msg}: ${val1}${result ? " == " : " != "}${val2}`);
}

function todo(id, text) {
  gResults.todo();
  append(id, `[TODO] ${text}\n`);
}

function resultColor(id) {
  const status = gResults.failures > 0 ? "failure" : gResults.todos > 0 ? "todo" : "success";
  $(id).classList.remove("success", "todo", "failure");
  $(id).classList.add(status);
}

// Copies a view's bytes into a standalone ArrayBuffer.
function getArrayBuffer(buf) {
  return ArrayBuffer.isView(buf) ? new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength).slice().buffer : buf;
}

function toBytes(buf) {
  return ArrayBuffer.isView(buf) ? new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength) : new Uint8Array(buf);
}

function hexEncode(buf) {
  return Array.from(toBytes(buf), x => x.toString(16).padStart(2, "0")).join("");
}

function b64(buf) {
  return btoa(Array.from(toBytes(buf), x => String.fromCharCode(x)).join(""));
}

function b64enc(buf) {
  return b64(buf).replace(/\+/g, "-").replace(/\//g, "_").replace(/=/g, "");
}

function string2buffer(str) {
  return new TextEncoder().encode(str);
}

function buffer2string(buf) {
  return new TextDecoder().decode(buf);
}

// JSON.stringify replacer that shows binary fields as base64url.
function jsonBytes(key, value) {
  return (value instanceof ArrayBuffer || ArrayBuffer.isView(value)) ? b64enc(value) : value;
}

async function sha256(data) {
  return new Uint8Array(await crypto.subtle.digest("SHA-256", data));
}

function concatBytes(...parts) {
  const out = new Uint8Array(parts.reduce((sum, part) => sum + toBytes(part).length, 0));
  let offset = 0;
  for (const part of parts) {
    out.set(toBytes(part), offset);
    offset += toBytes(part).length;
  }
  return out;
}

function assembleRegistrationSignedData(rpIdHash, clientDataHash, credId, publicKeyBytes) {
  return concatBytes([0x00], rpIdHash, clientDataHash, credId, publicKeyBytes);
}

function assemblePublicKeyBytesData(xCoord, yCoord) {
  // Produce an uncompressed EC key point. These start with 0x04, and then
  // two 32-byte numbers denoting X and Y.
  if (!(xCoord instanceof Uint8Array && yCoord instanceof Uint8Array)
      || xCoord.length != 32 || yCoord.length != 32) {
    throw new Error("Coordinates must be 32-byte byte strings");
  }
  return concatBytes([0x04], xCoord, yCoord);
}

// Kept on window so the parsed values can be inspected from the console.
const state = window.state = {
  createRequest: null,
  createResponse: null,
  publicKey: null,
  keyHandle: null,
};

function isCborMap(aValue) {
  return aValue instanceof Map;
}

const dnNames = { "2.5.4.3": "CN", "2.5.4.6": "C", "2.5.4.7": "L", "2.5.4.8": "ST", "2.5.4.10": "O", "2.5.4.11": "OU" };

function formatName(name) {
  return name.typesAndValues
             .map(tv => `${dnNames[tv.type] ?? tv.type}=${tv.value.valueBlock.value}`)
             .join(", ");
}

async function webAuthnDecodeCBORAttestation(aCborAttBuf, aClientDataJSON) {
  const attObj = CBOR.decode(aCborAttBuf);
  console.log(":: Attestation CBOR Object ::", attObj);
  if (!isCborMap(attObj)) {
    throw new Error("Invalid CBOR Attestation Object");
  }
  const fmt = attObj.get("fmt");
  const authData = attObj.get("authData");
  const attStmt = attObj.get("attStmt");
  if (!(typeof fmt === "string" && authData instanceof Uint8Array && isCborMap(attStmt))) {
    throw new Error("Invalid CBOR Attestation Object");
  }

  if (fmt == "fido-u2f") {
    const sig = attStmt.get("sig");
    const x5c = attStmt.get("x5c");
    if (!(sig instanceof Uint8Array && Array.isArray(x5c) && x5c.every(c => c instanceof Uint8Array))) {
      throw new Error("Invalid CBOR Attestation Statement");
    }

    append("createOut", "\n:: FIDO-U2F Attestation Format ::\n");
    const attestation = await webAuthnDecodeAuthDataArray(authData);

    append("createOut", "\n:: Attestation Certificate Information ::\n");
    if (x5c.length != 1) {
      throw new Error("Can't yet handle cert chains != 1 cert long");
    }

    const certDER = b64(x5c[0]);
    append("createOut", `PEM-encoded Certificate:\n-----BEGIN CERTIFICATE-----\n${certDER.replace(/(.{60})/g, "$1\n")}\n-----END CERTIFICATE-----\n`);
    console.log("DER-encoded Certificate: ", certDER);

    const certAsn1 = fromBER(getArrayBuffer(x5c[0]));
    if (!test("createOut", asn1Okay(certAsn1, x5c[0].byteLength), "Attestation Certificate parsed")) {
      throw new Error("Attestation Certificate didn't parse correctly.");
    }

    const cert = state.attestationCert = new Certificate({ schema: certAsn1.result });
    append("createOut", "Attestation Cert\n");
    append("createOut", `Subject: ${formatName(cert.subject)}\n`);
    append("createOut", `Issuer: ${formatName(cert.issuer)}\n`);
    append("createOut", `Validity: ${cert.notBefore.value.toISOString()} to ${cert.notAfter.value.toISOString()}\n`);

    try {
      test("createOut", await cert.verify(), "Attestation certificate signature verified successfully");
    } catch (error) {
      append("createOut", `[NOTE] Attestation cert signature verification couldn't continue, probably because of a lack of issuer cert: ${error}\n`);
    }

    const certKeyInfo = cert.subjectPublicKeyInfo;
    if (certKeyInfo.algorithm.algorithmId != "1.2.840.10045.2.1"
        || certKeyInfo.algorithm.algorithmParams?.valueBlock?.toString() != "1.2.840.10045.3.1.7") {
      throw new Error("Attestation certificate key must be an EC P-256 key");
    }

    state.attestationSig = sig;
    const { r, s } = parseDerSignature(sig);
    test("createOut", true, "Attestation Signature parsed");
    append("createOut", "Attestation Signature (by the key in the cert, over the new credential):\n");
    append("createOut", `R-component: ${hexEncode(r)}\n`);
    append("createOut", `S-component: ${hexEncode(s)}\n`);

    const certPubKey = await importPublicKey(certKeyInfo.subjectPublicKey.valueBlock.valueHexView);
    const signedData = assembleRegistrationSignedData(attestation.rpIdHash, await sha256(aClientDataJSON),
                                                      attestation.attestationAuthData.credId,
                                                      attestation.publicKeyBytes);
    const verified = await verifySignature(certPubKey, signedData, sig);
    test("createOut", verified, "Attestation signature verified with the certificate's key");

    attestation.attestationObject = attObj;
    return attestation;
  }

  if (fmt == "none") {
    if (attStmt.size != 0) {
      throw new Error("none attestation must have an empty attStmt");
    }
    append("createOut", "\n:: None Attestation Format ::\n");
    const attestation = await webAuthnDecodeAuthDataArray(authData);
    attestation.attestationObject = attObj;
    return attestation;
  }

  throw new Error(`Unknown attestation format: ${fmt}`);
}

function decodeExtensions(aBytes) {
  if (aBytes.length == 0) {
    throw new Error("Extension Data flag was set, but no extensions were passed in");
  }
  const extensions = CBOR.decode(getArrayBuffer(aBytes));
  if (!isCborMap(extensions)) {
    throw new Error("Extensions must be a CBOR map");
  }
  console.log("Extensions: ", extensions);
  return extensions;
}

async function webAuthnDecodeAuthDataArray(aAuthData) {
  aAuthData = toBytes(aAuthData).slice();
  if (aAuthData.length < 37) {
    throw new Error(`Authenticator data is too short: ${aAuthData.length} bytes`);
  }

  const rpIdHash = aAuthData.slice(0, 32);
  const flags = aAuthData.slice(32, 33);
  const counter = aAuthData.slice(33, 37);

  console.log(":: Attestation Object Data ::");
  console.log(`RP ID Hash: ${hexEncode(rpIdHash)}`);
  console.log(`Counter: ${hexEncode(counter)} Flags: ${flags[0]}`);

  if ((flags[0] & flag_AT) == 0x00) {
    // No Attestation Data, so only extensions can follow the counter.
    const result = { rpIdHash, flags, counter };
    if (flags[0] & flag_ED) {
      result.extensions = decodeExtensions(aAuthData.subarray(37));
    } else if (aAuthData.length != 37) {
      throw new Error(`Unexpected ${aAuthData.length - 37} bytes after the counter`);
    }
    return result;
  }

  if (aAuthData.length < 55) {
    throw new Error("Attestation Data flag was set, but not enough data passed in!");
  }

  const attData = {};
  attData.aaguid = aAuthData.slice(37, 53);
  attData.credIdLen = (aAuthData[53] << 8) + aAuthData[54];
  if (aAuthData.length < 55 + attData.credIdLen) {
    throw new Error(`Credential ID length ${attData.credIdLen} exceeds authenticator data`);
  }
  attData.credId = aAuthData.slice(55, 55 + attData.credIdLen);

  console.log(":: Attestation Data ::");
  console.log(`AAGUID: ${hexEncode(attData.aaguid)}`);

  const keyOffset = 55 + attData.credIdLen;
  const { value: pubkeyObj, length: keyLength } = CBOR.decodeFirst(getArrayBuffer(aAuthData.subarray(keyOffset)));
  if (flags[0] & flag_ED) {
    attData.extensions = decodeExtensions(aAuthData.subarray(keyOffset + keyLength));
  } else if (aAuthData.length != keyOffset + keyLength) {
    throw new Error(`Unexpected ${aAuthData.length - keyOffset - keyLength} bytes after the public key`);
  }
  if (!(isCborMap(pubkeyObj) && pubkeyObj.has(cose_kty) && pubkeyObj.has(cose_alg) && pubkeyObj.has(cose_crv)
        && pubkeyObj.has(cose_crv_x) && pubkeyObj.has(cose_crv_y))) {
    throw new Error("Invalid CBOR Public Key Object");
  }
  if (pubkeyObj.get(cose_kty) !== cose_kty_ec2) {
    throw new Error("Unexpected key type");
  }
  if (pubkeyObj.get(cose_alg) !== cose_alg_ECDSA_w_SHA256) {
    throw new Error("Unexpected public key algorithm");
  }
  if (pubkeyObj.get(cose_crv) !== cose_crv_P256) {
    throw new Error("Unexpected curve");
  }

  const pubKeyBytes = assemblePublicKeyBytesData(pubkeyObj.get(cose_crv_x), pubkeyObj.get(cose_crv_y));
  console.log(":: CBOR Public Key Object Data ::");
  console.log(`kty: ${pubkeyObj.get(cose_kty)} (EC2)`);
  console.log(`alg: ${pubkeyObj.get(cose_alg)} (ES256)`);
  console.log(`crv: ${pubkeyObj.get(cose_crv)} (P256)`);
  console.log(`X: ${hexEncode(pubkeyObj.get(cose_crv_x))}`);
  console.log(`Y: ${hexEncode(pubkeyObj.get(cose_crv_y))}`);
  console.log(`Uncompressed (hex): ${hexEncode(pubKeyBytes)}`);

  return {
    rpIdHash,
    flags,
    counter,
    attestationAuthData: attData,
    publicKeyBytes: pubKeyBytes,
    publicKeyHandle: await importPublicKey(pubKeyBytes),
  };
}

function importPublicKey(keyBytes) {
  if (keyBytes[0] != 0x04 || keyBytes.byteLength != 65) {
    throw new Error("Bad public key octet string");
  }
  const jwk = {
    kty: "EC",
    crv: "P-256",
    x: b64enc(keyBytes.subarray(1, 33)),
    y: b64enc(keyBytes.subarray(33)),
  };
  return crypto.subtle.importKey("jwk", jwk, { name: "ECDSA", namedCurve: "P-256" }, true, ["verify"]);
}

function derIntegerToBytes32(der, offset) {
  if (der[offset] != 0x02) {
    throw new Error(`Invalid signature: expected INTEGER at offset ${offset}`);
  }
  const len = der[offset + 1];
  let value = der.subarray(offset + 2, offset + 2 + len);
  if (len < 1 || value.length != len) {
    throw new Error(`Invalid signature: truncated INTEGER at offset ${offset}`);
  }
  if (value[0] & 0x80) {
    throw new Error(`Invalid signature: negative INTEGER at offset ${offset}`);
  }
  if (value.length > 1 && value[0] == 0x00) {
    if (!(value[1] & 0x80)) {
      throw new Error(`Invalid signature: non-minimal INTEGER at offset ${offset}`);
    }
    value = value.subarray(1);
  }
  if (value.length > 32) {
    throw new Error("Invalid signature: INTEGER longer than 32 bytes");
  }
  const bytes = new Uint8Array(32);
  bytes.set(value, 32 - value.length);
  return { bytes, next: offset + 2 + len };
}

// Parses a DER ECDSA-Sig-Value into 32-byte R and S components.
function parseDerSignature(derSig) {
  const der = toBytes(derSig);
  if (der.length < 8 || der[0] != 0x30 || der[1] != der.length - 2) {
    console.log(`bad sig: ${hexEncode(der)}`);
    throw new Error(`Invalid signature encoding (length ${der.length})`);
  }
  const r = derIntegerToBytes32(der, 2);
  const s = derIntegerToBytes32(der, r.next);
  if (s.next != der.length) {
    throw new Error("Invalid signature: trailing bytes after S");
  }
  return { r: r.bytes, s: s.bytes };
}

function verifySignature(key, data, derSig) {
  const { r, s } = parseDerSignature(derSig);
  const sig = concatBytes(r, s);

  console.log("key:    ", key);
  console.log("data:   ", hexEncode(data));
  console.log("derSig: ", hexEncode(derSig));
  console.log("sig:    ", hexEncode(sig));

  return crypto.subtle.verify({ name: "ECDSA", hash: "SHA-256" }, key, sig, data);
}

function asn1Okay(asn1, expectedLength) {
  if (asn1.offset === -1) {
    append("createOut", `Error: ${asn1.result.error}\n`);
    return false;
  }
  if (asn1.result.warnings.length > 0) {
    append("createOut", `Warning: ${asn1.result.warnings}\n`);
    return false;
  }
  if (asn1.offset != expectedLength) {
    append("createOut", `Error: ${expectedLength - asn1.offset} unexpected trailing bytes\n`);
    return false;
  }
  return true;
}

function reportError(id, aErr) {
  if (aErr?.name == "AbortError") {
    gResults.reset();
    append(id, "Aborted; retry?\n");
  } else {
    gResults.fail();
    append(id, `Got error:\n${aErr}\n\n`);
  }
}

async function doWebAuthnCreate(challengeBytes) {
  const createRequest = {
    challenge: challengeBytes,
    rp: {
      name: "Acme",
    },
    user: {
      id: string2buffer("1098237235409872"),
      name: "john.p.smith@example.com",
      displayName: "John P. Smith",
    },

    pubKeyCredParams: [
      {
        alg: cose_alg_ECDSA_w_SHA256,
        type: "public-key",
      },
    ],

    authenticatorSelection: {
      authenticatorAttachment: "cross-platform",
      residentKey: "discouraged",
      requireResidentKey: false,
      userVerification: "preferred",
    },

    timeout: 60000,
    excludeCredentials: [],
  };

  let rpid = window.location.hostname;
  if ($("rpIdText").value) {
    rpid = createRequest.rp.id = $("rpIdText").value;
  }

  if ($("attestationType").value) {
    createRequest.attestation = $("attestationType").value;
  }

  state.createRequest = createRequest;
  state.keyHandle = null;
  state.publicKey = null;

  console.log(`let createRequest = ${JSON.stringify(createRequest, jsonBytes, 2)}`);
  console.log("navigator.credentials.create({ publicKey: createRequest })");

  try {
    const credential = state.createResponse = await navigator.credentials.create({ publicKey: createRequest });
    append("createOut", "Note: Raw response in console.\n");
    console.log("Credentials.Create response: ", credential);

    const attestation = await webAuthnDecodeCBORAttestation(credential.response.attestationObject,
                                                            credential.response.clientDataJSON);

    testEqual("createOut", b64enc(await sha256(string2buffer(rpid))), b64enc(attestation.rpIdHash),
              "Calculated RP ID hash must match what the browser derived.");

    const flags = attestation.flags[0];
    if (!testEqual("createOut", flags & (flag_TUP | flag_AT), (flag_TUP | flag_AT), "User presence and Attestation Object must both be set")) {
      throw new Error("Attestation is missing the user presence or attested credential data flag.");
    }
    testEqual("createOut", hexEncode(attestation.attestationAuthData.credId), hexEncode(credential.rawId), "Credential ID from CBOR and Raw ID match");
    state.keyHandle = credential.rawId;
    append("createOut", `Keypair Identifier: ${hexEncode(state.keyHandle)}\n`);
    append("createOut", `Public Key: ${hexEncode(attestation.publicKeyBytes)}\n`);

    state.publicKey = attestation.publicKeyHandle;

    append("createOut", "\n:: CBOR Attestation Object Data ::\n");
    append("createOut", `RP ID Hash: ${hexEncode(attestation.rpIdHash)}\n`);
    append("createOut", `Counter: ${hexEncode(attestation.counter)} Flags: ${flags}\n`);
    append("createOut", `AAGUID: ${hexEncode(attestation.attestationAuthData.aaguid)}\n`);

    append("createOut", "\n:: Client Data Information ::\n");
    const clientData = JSON.parse(buffer2string(credential.response.clientDataJSON));
    append("createOut", "Client Data object, in full:\n");
    append("createOut", `${JSON.stringify(clientData, null, 2)}\n\n`);

    testEqual("createOut", b64enc(challengeBytes), clientData.challenge, "Challenge matches");
    if ("androidPackageName" in clientData) {
      append("createOut", `Android origin is: ${clientData.origin} (unchecked)\n`);
    } else {
      testEqual("createOut", window.location.origin, clientData.origin, "ClientData.origin matches this origin (WD-06)");
    }
    if ("type" in clientData) {
      testEqual("createOut", "webauthn.create", clientData.type, "Type is valid (WD-08)");
    } else {
      todo("createOut", "clientData.type is not set (WD-08)");
    }

    append("createOut", "\n\nRaw request:\n");
    append("createOut", `${JSON.stringify(createRequest, jsonBytes, 2)}\n\n`);
  } catch (aErr) {
    reportError("createOut", aErr);
  }
  resultColor("createOut");
  append("createOut", `${gResults}\n\n`);
}

async function doWebAuthnGet() {
  $("getOut").textContent = "";
  gResults.reset();

  if (!state.publicKey) {
    gResults.fail();
    append("getOut", "Need to make a credential first:\n");
    return;
  }

  $("getOut").textContent = "Contacting token... please perform your verification gesture (e.g., touch it, or plug it in)\n\n";

  const newCredential = {
    type: "public-key",
    id: state.keyHandle,
    transports: ["usb", "nfc", "ble"],
  };
  console.log("New Credential: ", newCredential);

  const challengeBytes = crypto.getRandomValues(new Uint8Array(16));

  const publicKeyCredentialRequestOptions = {
    challenge: challengeBytes,
    timeout: 60000,
    allowCredentials: [newCredential],
    userVerification: "preferred",
    extensions: {},
  };

  const appId = $("appIdText").value;
  if (appId) {
    publicKeyCredentialRequestOptions.extensions.appid = appId;
  }

  let rpid = window.location.hostname;
  if ($("rpIdText").value) {
    rpid = publicKeyCredentialRequestOptions.rpId = $("rpIdText").value;
  }

  try {
    const assertion = await navigator.credentials.get({ publicKey: publicKeyCredentialRequestOptions });
    console.log("Credentials.Get response: ", assertion);
    append("getOut", "Raw response in console.\n");

    const clientData = JSON.parse(buffer2string(assertion.response.clientDataJSON));
    testEqual("getOut", clientData.challenge, b64enc(challengeBytes), "Challenge is identical");
    if ("androidPackageName" in clientData) {
      append("getOut", `Android origin is: ${clientData.origin} (unchecked)\n`);
    } else {
      testEqual("getOut", window.location.origin, clientData.origin, "ClientData.origin matches this origin (WD-06)");
    }
    if ("type" in clientData) {
      testEqual("getOut", "webauthn.get", clientData.type, "Type is valid (WD-08)");
    } else {
      todo("getOut", "clientData.type is not set (WD-08)");
    }

    const extensionResults = assertion.getClientExtensionResults();
    append("getOut", `Extensions: ${JSON.stringify(extensionResults)}\n`);

    const authData = await webAuthnDecodeAuthDataArray(assertion.response.authenticatorData);
    const flags = authData.flags[0];
    if (!testEqual("getOut", flags & flag_TUP, flag_TUP, "User presence flag must be set")) {
      throw new Error("Assertion's user presence byte not set correctly.");
    }

    testEqual("getOut", authData.counter.byteLength, 4, "Counter must be 4 bytes");

    append("getOut", "\n:: CBOR Attestation Object Data ::\n");
    append("getOut", `RP ID Hash: ${hexEncode(authData.rpIdHash)}\n`);
    append("getOut", `Counter: ${hexEncode(authData.counter)} Flags: ${flags}\n`);
    append("getOut", "\n");

    let hashedId = rpid;
    if (extensionResults.appid) {
      hashedId = appId;
      append("getOut", `AppID extension set, using ${appId} as the value to hash\n`);
    }

    const appParam = await sha256(string2buffer(hashedId));
    const clientDataHash = await sha256(assertion.response.clientDataJSON);
    testEqual("getOut", b64enc(appParam), b64enc(authData.rpIdHash),
              "Calculated RP ID hash must match what the browser derived.");
    append("getOut", `ClientData buffer: ${hexEncode(assertion.response.clientDataJSON)}\n\n`);
    append("getOut", `ClientDataHash: ${hexEncode(clientDataHash)}\n\n`);

    const signedData = concatBytes(assertion.response.authenticatorData, clientDataHash);
    append("getOut", `Signed Data assembled: ${hexEncode(signedData)}\n`);
    const signatureValid = await verifySignature(state.publicKey, signedData, assertion.response.signature);
    test("getOut", signatureValid, "The token signature must be valid.");
  } catch (aErr) {
    reportError("getOut", aErr);
  }

  append("getOut", "\n\nRaw request:\n");
  append("getOut", `${JSON.stringify(publicKeyCredentialRequestOptions, jsonBytes, 2)}\n\n`);
  resultColor("getOut");
  append("getOut", `${gResults}\n\n`);
}

if (!window.PublicKeyCredential) {
  $("error").textContent = "Web Authentication API not found";
  document.querySelectorAll("button").forEach(button => button.classList.add("inactive"));
}

if (!window.isSecureContext) {
  $("error").textContent = "Loaded outside of a secure context. It shouldn't work.";
}

$("createButton").addEventListener("click", () => {
  $("createOut").textContent = "Contacting token... please perform your verification gesture (e.g., touch it, or plug it in)\n\n";
  gResults.reset();

  const challengeBytes = crypto.getRandomValues(new Uint8Array(16));

  do {
    doWebAuthnCreate(challengeBytes);
  } while ($("loopForever").checked);
});

$("getButton").addEventListener("click", doWebAuthnGet);
