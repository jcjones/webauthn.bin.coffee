/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this file,
 * You can obtain one at http://mozilla.org/MPL/2.0/. */

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

class ResultTracker {
  constructor() {
    this.reset()
  }
  reset() {
    this.failCount = 0;
    this.todoCount = 0;
  }
  fail() {
    this.failCount += 1;
  }
  todo() {
    this.todoCount += 1;
  }
  get failures() {
    return this.failCount;
  }
  get todos() {
    return this.todoCount;
  }
  toString() {
    return "Failures: " + this.failures + " TODOs: " + this.todos;
  }
}

var gResults = new ResultTracker()

function append(id, text) {
  $("#"+id).text($("#"+id).text() + text);
}

function test(id, test, text) {
  if (!test) { gResults.fail(); }
  let message = (test)? "[PASS]" : "[FAIL]";
  message += " " + text + "\n";
  append(id, message);
  return test;
}

function testEqual(id, val1, val2, msg) {
  let result = (val1 == val2);
  let cmp = (result)? " == " : " != ";
  return test(id, result, msg + ": " + val1 + cmp + val2);
}

function todo(id, text) {
  gResults.todo();
  append(id, "[TODO] " + text + "\n");
}

function getArrayBuffer(buf) {
  if (buf.constructor === Uint8Array) {
    // buf is a shared array, and we want to make copies of particular parts
    // for our ArrayBuffer views.
    return buf.slice(0, buf.byteLength).buffer;
  }
  return buf;
}

function resultColor(id) {
  if (gResults.failures == 0) {
    if (gResults.todos == 0) {
      $("#"+id).removeClass("failure"); $("#"+id).removeClass("todo"); $("#"+id).addClass("success");
    } else {
      $("#"+id).removeClass("failure"); $("#"+id).removeClass("success"); $("#"+id).addClass("todo");
    }
  } else {
    $("#"+id).removeClass("success"); $("#"+id).removeClass("todo"); $("#"+id).addClass("failure");
  }
}

function hexEncode(buf) {
  if (!(buf.constructor === Uint8Array)) {
    buf = new Uint8Array(buf);
  }
  return Array.from(buf)
              .map(function(x){ return ("0"+x.toString(16)).substr(-2) })
              .join("");
}

function b64enc(buf) {
  return base64js.fromByteArray(buf)
                 .replace(/\+/g, "-")
                 .replace(/\//g, "_")
                 .replace(/=/g, "");
}

function string2buffer(str) {
  return new TextEncoder().encode(str);
}

function buffer2string(buf) {
  return new TextDecoder().decode(buf);
}

function deriveAppAndChallengeParam(appId, clientData, attestation) {
  var appIdBuf = string2buffer(appId);
  return Promise.all([
    crypto.subtle.digest("SHA-256", appIdBuf),
    crypto.subtle.digest("SHA-256", clientData)
  ])
  .then(function(digests) {
    return {
      appParam: new Uint8Array(digests[0]),
      challengeParam: new Uint8Array(digests[1]),
      attestation: attestation
    };
  });
}

function assembleSignedData(appParam, flags, counter, challengeParam) {
  let signedData = new Uint8Array(32 + 1 + 4 + 32);
  new Uint8Array(appParam).map((x, i) => signedData[0 + i] = x);
  signedData[32] = new Uint8Array(flags)[0];
  new Uint8Array(counter).map((x, i) => signedData[33 + i] = x);
  new Uint8Array(challengeParam).map((x, i) => signedData[37 + i] = x);
  return signedData;
}

function assembleRegistrationSignedData(appParam, challengeParam, keyHandle, pubKey) {
  let signedData = new Uint8Array(1 + 32 + 32 + keyHandle.length + 65);
  signedData[0] = 0x00;
  new Uint8Array(appParam).map((x, i) => signedData[1 + i] = x);
  new Uint8Array(challengeParam).map((x, i) => signedData[33 + i] = x);
  new Uint8Array(keyHandle).map((x, i) => signedData[65 + i] = x);
  new Uint8Array(pubKey).map((x, i) => signedData[65 + keyHandle.length + i] = x);
  return signedData;
}

function assemblePublicKeyBytesData(xCoord, yCoord) {
  // Produce an uncompressed EC key point. These start with 0x04, and then
  // two 32-byte numbers denoting X and Y.
  if (!(xCoord instanceof Uint8Array && yCoord instanceof Uint8Array)
      || xCoord.length != 32 || yCoord.length != 32) {
    throw ("Coordinates must be 32-byte byte strings");
  }
  let keyBytes = new Uint8Array(65);
  keyBytes[0] = 0x04;
  xCoord.map((x, i) => keyBytes[1 + i] = x);
  yCoord.map((x, i) => keyBytes[33 + i] = x);
  return keyBytes;
}

var state = {
  // Raw messages
  createRequest: null,
  createResponse: null,

  // Parsed values
  publicKey: null,
  keyHandle: null,
}

function isCborMap(aValue) {
  return aValue !== null && typeof aValue === "object"
         && !Array.isArray(aValue) && !(aValue instanceof Uint8Array);
}

function webAuthnDecodeCBORAttestation(aCborAttBuf, aClientDataJSON) {
  let attObj = CBOR.decode(aCborAttBuf);
  console.log(":: Attestation CBOR Object ::");
  if (!(isCborMap(attObj) && typeof attObj.fmt === "string"
        && attObj.authData instanceof Uint8Array && isCborMap(attObj.attStmt))) {
    throw "Invalid CBOR Attestation Object";
  }

  if (attObj.fmt == "fido-u2f") {
    if (!(attObj.attStmt.sig instanceof Uint8Array && Array.isArray(attObj.attStmt.x5c)
          && attObj.attStmt.x5c.every(c => c instanceof Uint8Array))) {
      throw "Invalid CBOR Attestation Statement";
    }

    append("createOut", "\n:: FIDO-U2F Attestation Format ::\n");
    return webAuthnDecodeAuthDataArray(new Uint8Array(attObj.authData))
    .then(async function (aAttestationObj) {

      /* Decode U2F Attestation Certificates */
      append("createOut", "\n:: Attestation Certificate Information ::\n");
      if (attObj.attStmt.x5c.length != 1) {
        throw "Can't yet handle cert chains != 1 cert long";
      }

      let attestationCertDER = base64js.fromByteArray(attObj.attStmt.x5c[0]);
      append("createOut", "PEM-encoded Certificate:\n-----BEGIN CERTIFICATE-----\n" + attestationCertDER.replace(/(.{60})/g, "$1\n") + "\n-----END CERTIFICATE-----\n");
      console.log("DER-encoded Certificate: ", attestationCertDER);

      let certAsn1 = org.pkijs.fromBER(getArrayBuffer(attObj.attStmt.x5c[0]));
      if (!test("createOut", asn1Okay(certAsn1), "Attestation Certificate parsed")) {
        throw "Attestation Certificate didn't parse correctly.";
      }

      state.attestationCert = new org.pkijs.simpl.CERT({ schema: certAsn1.result });
      append("createOut", "Attestation Cert\n");
      append("createOut", "Subject: " + state.attestationCert.subject.types_and_values[0].value.value_block.value + "\n");
      append("createOut", "Issuer: " + state.attestationCert.issuer.types_and_values[0].value.value_block.value + "\n");
      append("createOut", "Validity (in millis): " + (state.attestationCert.notAfter.value - state.attestationCert.notBefore.value + "\n"));

      state.attestationSig = attObj.attStmt.sig;
      let sigAsn1 = org.pkijs.fromBER(getArrayBuffer(state.attestationSig));
      if (!test("createOut", asn1Okay(sigAsn1), "Attestation Signature parsed")) {
        throw "Attestation Signature failed to validate";
      }

      await state.attestationCert.verify()
      .then((result) => {
        test("createOut", result, "Attestation certificate signature verified successfully");
      })
      .catch((error) => {
        append("createOut", "[NOTE] Attestation cert signature verification couldn't continue, probably because of a lack of issuer cert: " + error + "\n");
      });

      testEqual("createOut", sigAsn1.result.block_length, state.attestationSig.byteLength, "Signature buffer has no unnecessary bytes.");

      append("createOut", "Attestation Signature (by the key in the cert, over the new credential):\n");
      let [R, S] = ecdsaSigComponents(sigAsn1);
      append("createOut", "R-component: " + hexEncode(R) + "\n");
      append("createOut", "S-component: " + hexEncode(S) + "\n");

      let certPubKey = await importPublicKey(new Uint8Array(state.attestationCert.subjectPublicKeyInfo.subjectPublicKey.value_block.value_hex));
      let clientDataHash = await crypto.subtle.digest("SHA-256", aClientDataJSON);
      let signedData = assembleRegistrationSignedData(aAttestationObj.rpIdHash, clientDataHash,
                                                      aAttestationObj.attestationAuthData.credId,
                                                      aAttestationObj.publicKeyBytes);
      let verified = await verifySignature(certPubKey, signedData, state.attestationSig);
      test("createOut", verified, "Attestation signature verified with the certificate's key");

      aAttestationObj.attestationObject = attObj;
      return aAttestationObj;
    });
  }

  if (attObj.fmt == "none") {
    if (Object.keys(attObj.attStmt).length != 0) {
      throw "\"none\" attestation must have an empty attStmt";
    }
    append("createOut", "\n:: \"None\" Attestation Format ::\n");
    return webAuthnDecodeAuthDataArray(new Uint8Array(attObj.authData))
    .then(function (aAttestationObj) {
      aAttestationObj.attestationObject = attObj;
      return aAttestationObj;
    });
  }

  return Promise.reject("Unknown attestation format: " + attObj.fmt)
}

// CBOR.decode rejects trailing bytes, so find where the first item ends.
function cborFirstItemLength(aBytes) {
  for (let end = 1; end <= aBytes.length; end++) {
    try {
      CBOR.decode(getArrayBuffer(aBytes.slice(0, end)));
      return end;
    } catch (e) {
      // A RangeError means the item runs past `end`; anything else is malformed.
      if (!(e instanceof RangeError)) {
        throw e;
      }
    }
  }
  throw "No complete CBOR item found";
}

function decodeExtensions(aBytes) {
  if (aBytes.length == 0) {
    throw "Extension Data flag was set, but no extensions were passed in";
  }
  let extensions = CBOR.decode(getArrayBuffer(aBytes));
  if (!isCborMap(extensions)) {
    throw "Extensions must be a CBOR map";
  }
  console.log("Extensions: ", extensions);
  return extensions;
}

function webAuthnDecodeAuthDataArray(aAuthData) {
  if (!(aAuthData instanceof Uint8Array)) {
    aAuthData = new Uint8Array(aAuthData);
  }
  if (aAuthData.length < 37) {
    throw "Authenticator data is too short: " + aAuthData.length + " bytes";
  }

  let rpIdHash = aAuthData.slice(0, 32);
  let flags = aAuthData.slice(32, 33);
  let counter = aAuthData.slice(33, 37);

  console.log(":: Attestation Object Data ::");
  console.log("RP ID Hash: " + hexEncode(rpIdHash));
  console.log("Counter: " + hexEncode(counter) + " Flags: " + flags);

  if ((flags[0] & flag_AT) == 0x00) {
    // No Attestation Data, so only extensions can follow the counter.
    let result = {
      rpIdHash: rpIdHash,
      flags: flags,
      counter: counter,
    };
    if (flags[0] & flag_ED) {
      result.extensions = decodeExtensions(aAuthData.slice(37));
    } else if (aAuthData.length != 37) {
      throw "Unexpected " + (aAuthData.length - 37) + " bytes after the counter";
    }
    return Promise.resolve(result);
  }

  if (aAuthData.length < 55) {
    throw "Attestation Data flag was set, but not enough data passed in!";
  }

  let attData = {};
  attData.aaguid = aAuthData.slice(37, 53);
  attData.credIdLen = (aAuthData[53] << 8) + aAuthData[54];
  if (aAuthData.length < 55 + attData.credIdLen) {
    throw "Credential ID length " + attData.credIdLen + " exceeds authenticator data";
  }
  attData.credId = aAuthData.slice(55, 55 + attData.credIdLen);

  console.log(":: Attestation Data ::");
  console.log("AAGUID: " + hexEncode(attData.aaguid));

  let cborPubKey = aAuthData.slice(55 + attData.credIdLen);
  if (flags[0] & flag_ED) {
    let keyLength = cborFirstItemLength(cborPubKey);
    attData.extensions = decodeExtensions(cborPubKey.slice(keyLength));
    cborPubKey = cborPubKey.slice(0, keyLength);
  }
  var pubkeyObj = CBOR.decode(getArrayBuffer(cborPubKey));
  if (!(isCborMap(pubkeyObj) && cose_kty in pubkeyObj && cose_alg in pubkeyObj && cose_crv in pubkeyObj
        && cose_crv_x in pubkeyObj && cose_crv_y in pubkeyObj)) {
    throw "Invalid CBOR Public Key Object";
  }
  if (pubkeyObj[cose_kty] !== cose_kty_ec2) {
    throw "Unexpected key type";
  }
  if (pubkeyObj[cose_alg] !== cose_alg_ECDSA_w_SHA256) {
    throw "Unexpected public key algorithm";
  }
  if (pubkeyObj[cose_crv] !== cose_crv_P256) {
    throw "Unexpected curve";
  }

  let pubKeyBytes = assemblePublicKeyBytesData(pubkeyObj[cose_crv_x], pubkeyObj[cose_crv_y]);
  console.log(":: CBOR Public Key Object Data ::");
  console.log("kty: " + pubkeyObj[cose_kty] + " (EC2)");
  console.log("alg: " + pubkeyObj[cose_alg] + " (ES256)");
  console.log("crv: " + pubkeyObj[cose_crv] + " (P256)");
  console.log("X: " + pubkeyObj[cose_crv_x]);
  console.log("Y: " + pubkeyObj[cose_crv_y]);
  console.log("Uncompressed (hex): " + hexEncode(pubKeyBytes));

  return importPublicKey(pubKeyBytes)
  .then(function(aKeyHandle) {
    return {
      rpIdHash: rpIdHash,
      flags: flags,
      counter: counter,
      attestationAuthData: attData,
      publicKeyBytes: pubKeyBytes,
      publicKeyHandle: aKeyHandle,
    };
  });
}

function importPublicKey(keyBytes) {
  if (keyBytes[0] != 0x04 || keyBytes.byteLength != 65) {
    throw "Bad public key octet string";
  }
  let jwk = {
    kty: "EC",
    crv: "P-256",
    x: b64enc(keyBytes.subarray(1,33)),
    y: b64enc(keyBytes.subarray(33))
  };
  return crypto.subtle.importKey("jwk", jwk, {name: "ECDSA", namedCurve: "P-256"}, true, ["verify"])
}

function derIntegerToBytes32(der, offset) {
  if (der[offset] != 0x02) {
    throw "Invalid signature: expected INTEGER at offset " + offset;
  }
  let len = der[offset + 1];
  let value = der.subarray(offset + 2, offset + 2 + len);
  if (len < 1 || value.length != len) {
    throw "Invalid signature: truncated INTEGER at offset " + offset;
  }
  while (value.length > 32 && value[0] == 0x00) {
    value = value.subarray(1);
  }
  if (value.length > 32) {
    throw "Invalid signature: INTEGER longer than 32 bytes";
  }
  let bytes = new Uint8Array(32);
  bytes.set(value, 32 - value.length);
  return { bytes: bytes, length: len, next: offset + 2 + len };
}

function verifySignature(key, data, derSig) {
  let derSigArray = new Uint8Array(derSig);
  if (derSigArray.length < 8 || derSigArray[0] != 0x30 || derSigArray[1] != derSigArray.length - 2) {
    console.log("bad sig: " + hexEncode(derSigArray))
    throw "Invalid signature encoding (length " + derSigArray.length + ")";
  }

  let r = derIntegerToBytes32(derSigArray, 2);
  let s = derIntegerToBytes32(derSigArray, r.next);
  if (s.next != derSigArray.length) {
    throw "Invalid signature: trailing bytes after S";
  }
  let sig = new Uint8Array(64);
  sig.set(r.bytes, 0);
  sig.set(s.bytes, 32);

  console.log("lenR:   ", r.length, " lenS: ", s.length);
  console.log("key:    ", key);
  console.log("data:   ", data, hexEncode(data));
  console.log("derSig: ", derSigArray, hexEncode(derSigArray));
  console.log("sig:    ", sig, hexEncode(sig));

  let alg = {name: "ECDSA", hash: "SHA-256"};
  return crypto.subtle.verify(alg, key, sig, data);
}

function asn1Okay(asn1) {
  if (asn1.result.error.length > 0) {
    console.log("Error: " + asn1.result.error);
    append("createOut", "Error: " + asn1.result.error + "\n");
    return false;
  }
  if (asn1.result.warnings.length > 0) {
    console.log("Warning: " + asn1.result.warnings.toString());
    append("createOut", "Warning: " + asn1.result.warnings.toString() + "\n");
    return false;
  }
  return true;
}

function ecdsaSigComponents(sigAsn1) {
  let parts = sigAsn1.result.value_block.value;
  if (!Array.isArray(parts) || parts.length != 2
      || !parts.every(p => p.value_block && p.value_block.value_hex)) {
    throw "Attestation signature is not a SEQUENCE of two INTEGERs";
  }
  return parts.map(p => new Uint8Array(p.value_block.value_hex));
}

function doWebAuthnCreate(challengeBytes) {
  let createRequest = {
    challenge: challengeBytes,
    // Relying Party:
    rp: {
      name: "Acme"
    },

    // User:
    user: {
      id: string2buffer("1098237235409872"),
      name: "john.p.smith@example.com",
      displayName: "John P. Smith",
    },

    pubKeyCredParams: [
      {
        alg: cose_alg_ECDSA_w_SHA256,
        type: "public-key",
      }
    ],

    authenticatorSelection: {
      authenticatorAttachment: "cross-platform",
      requireResidentKey: false,
      userVerification: "preferred"
    },

    attestation: undefined,
    timeout: 60000,  // 1 minute
    excludeCredentials: [], // No excludeList
  };

  let rpid = window.location.hostname;
  if ($("#rpIdText").val()) {
    rpid = $("#rpIdText").val();
    createRequest.rp.id = rpid;
  }

  if ($("#attestationType").val() != "") {
    createRequest.attestation = $("#attestationType").val();
  }

  state.createRequest = createRequest;

  console.log("let createRequest = " + JSON.stringify(createRequest, null, 2));
  console.log("navigator.credentials.create({ publicKey: createRequest })");

  navigator.credentials.create({ publicKey: createRequest })
  .then(function (aNewCredentialInfo) {
    state.createResponse = aNewCredentialInfo
    append("createOut", "Note: Raw response in console.\n");
    console.log("Credentials.Create response: ", aNewCredentialInfo);

    let buffer = getArrayBuffer(aNewCredentialInfo.response.attestationObject);
    return webAuthnDecodeCBORAttestation(buffer, aNewCredentialInfo.response.clientDataJSON);
  })
  .then(function (aAttestation) {
    // Make sure the RP ID hash matches what we calculate.
    return crypto.subtle.digest("SHA-256", string2buffer(rpid))
    .then(function(calculatedHash) {
      testEqual("createOut", b64enc(new Uint8Array(calculatedHash)), b64enc(aAttestation.rpIdHash),
         "Calculated RP ID hash must match what the browser derived.");
      return aAttestation;
    });
  })
  .then(function (aAttestation) {
    let flags = aAttestation.flags[0];
    if (!testEqual("createOut", flags & (flag_TUP | flag_AT), (flag_TUP | flag_AT), "User presence and Attestation Object must both be set")) {
      throw "Attestation is missing the user presence or attested credential data flag.";
    }
    testEqual("createOut", hexEncode(aAttestation.attestationAuthData.credId), hexEncode(state.createResponse.rawId), "Credential ID from CBOR and Raw ID match");
    state.keyHandle = state.createResponse.rawId;
    append("createOut", "Keypair Identifier: " + hexEncode(state.keyHandle) + "\n");
    append("createOut", "Public Key: " + hexEncode(aAttestation.publicKeyBytes) + "\n");

    state.publicKey = aAttestation.publicKeyHandle;

    append("createOut", "\n:: CBOR Attestation Object Data ::\n");
    append("createOut", "RP ID Hash: " + hexEncode(aAttestation.rpIdHash) + "\n");
    append("createOut", "Counter: " + hexEncode(aAttestation.counter) + " Flags: " + flags + "\n");
    append("createOut", "AAGUID: " + hexEncode(aAttestation.attestationAuthData.aaguid) + "\n");


    /* Decode Client Data */
    append("createOut", "\n:: Client Data Information ::\n");
    let clientData = JSON.parse(buffer2string(state.createResponse.response.clientDataJSON));
    append("createOut", "Client Data object, in full:\n");
    append("createOut", JSON.stringify(clientData, null, 2) + "\n\n");

    testEqual("createOut", b64enc(challengeBytes), clientData.challenge, "Challenge matches");
    if ("androidPackageName" in clientData) {
      append("createOut", `Android origin is: ${clientData.origin} (unchecked)\n`)
    } else {
      testEqual("createOut", window.location.origin, clientData.origin, "ClientData.origin matches this origin (WD-06)");
    }
    if ("type" in clientData) {
      testEqual("createOut", "webauthn.create", clientData.type, "Type is valid (WD-08)");
    } else {
      todo("createOut", "clientData.type is not set (WD-08)");
    }

  }).then(function (){
    append("createOut", "\n\nRaw request:\n");
    append("createOut", JSON.stringify(createRequest, null, 2) + "\n\n");
  }).catch(function (aErr) {
    if (aErr && (aErr.name == "AbortError" || aErr.name == "NS_ERROR_ABORT")) {
      gResults.reset();
      append("createOut", "Aborted; retry?\n");
    } else {
      gResults.fail();
      append("createOut", "Got error:\n");
      append("createOut", String(aErr) + "\n\n");
    }
  }).then(function (){
    resultColor("createOut");
    append("createOut", gResults.toString() + "\n\n");
  });
}

$(document).ready(function() {
  if (!window.PublicKeyCredential) {
    $("#error").text("Web Authentication API not found");
    $("button").addClass("inactive");
  }

  if (document.location.origin.startsWith("http://")) {
    $("#error").text("Loaded outside of a secure context. It shouldn't work.");
  }

  $("#createButton").click(function() {
    $("#createOut").text("Contacting token... please perform your verification gesture (e.g., touch it, or plug it in)\n\n");
    gResults.reset();

    let challengeBytes = new Uint8Array(16);
    window.crypto.getRandomValues(challengeBytes);

    do {
      doWebAuthnCreate(challengeBytes);
    } while($("#loopForever").prop("checked"));
  });

  $("#getButton").click(function() {
    $("#getOut").text("");
    gResults.reset();

    if (!state.createResponse) {
      gResults.fail();
      append("getOut", "Need to make a credential first:\n");
      return;
    }

    $("#getOut").text("Contacting token... please perform your verification gesture (e.g., touch it, or plug it in)\n\n");

    let newCredential = {
      type: "public-key",
      id: new Uint8Array(state.createResponse.rawId),
      transports: ["usb", "nfc", "ble"],
    }
    console.log("New Credential: ", newCredential);

    let challengeBytes = new Uint8Array(16);
    window.crypto.getRandomValues(challengeBytes);

    let publicKeyCredentialRequestOptions = {
      challenge: challengeBytes,
      timeout: 60000,
      allowCredentials: [newCredential],
      userVerification: "preferred",
      extensions: {}
    };

    if ($("#appIdText").val()) {
      publicKeyCredentialRequestOptions.extensions["appid"] = $("#appIdText").val();
    }

    let rpid = window.location.hostname;
    if ($("#rpIdText").val()) {
      rpid = $("#rpIdText").val();
      publicKeyCredentialRequestOptions.rpId = rpid;
    }

    navigator.credentials.get({publicKey: publicKeyCredentialRequestOptions})
    .then(function(aAssertion) {
      console.log("Credentials.Get response: ", aAssertion);
      append("getOut", "Raw response in console.\n");

      let clientData = JSON.parse(buffer2string(aAssertion.response.clientDataJSON));
      testEqual("getOut", clientData.challenge, b64enc(challengeBytes), "Challenge is identical");
      if ("androidPackageName" in clientData) {
        append("getOut", `Android origin is: ${clientData.origin} (unchecked)\n`)
      } else {
        testEqual("getOut", window.location.origin, clientData.origin, "ClientData.origin matches this origin (WD-06)");
      }
      if ("type" in clientData) {
        testEqual("getOut", "webauthn.get", clientData.type, "Type is valid (WD-08)");
      } else {
        todo("getOut", "clientData.type is not set (WD-08)");
      }

      let extensionResults = aAssertion.getClientExtensionResults();
      append("getOut", `Extensions: ${JSON.stringify(extensionResults)}\n`);

      return webAuthnDecodeAuthDataArray(aAssertion.response.authenticatorData)
      .then(function(aAttestation) {
        let flags = aAttestation.flags[0];
        if (!testEqual("getOut", flags & flag_TUP, flag_TUP, "User presence flag must be set")) {
          throw "Assertion's user presence byte not set correctly.";
        }

        testEqual("getOut", aAttestation.counter.byteLength, 4, "Counter must be 4 bytes");

        append("getOut", "\n:: CBOR Attestation Object Data ::\n");
        append("getOut", "RP ID Hash: " + hexEncode(aAttestation.rpIdHash) + "\n");
        append("getOut", "Counter: " + hexEncode(aAttestation.counter) + " Flags: " + flags + "\n");
        append("getOut", "\n");

        // Assemble the signed data and verify the signature
        let appId = rpid;
        if (extensionResults.appid) {
          appId = $("#appIdText").val();
          append("getOut", `AppID extension set, using ${appId} as the value to hash\n`);
        }

        return deriveAppAndChallengeParam(appId, aAssertion.response.clientDataJSON, aAttestation);
      })
      .then(function(aParams) {
        testEqual("getOut", b64enc(aParams.appParam), b64enc(new Uint8Array(aParams.attestation.rpIdHash)),
                  "Calculated RP ID hash must match what the browser derived.");
        append("getOut", "ClientData buffer: " + hexEncode(aAssertion.response.clientDataJSON) + "\n\n");
        append("getOut", "ClientDataHash: " + hexEncode(aParams.challengeParam) + "\n\n");
        return assembleSignedData(aParams.appParam, aParams.attestation.flags,
                                  aParams.attestation.counter, aParams.challengeParam);
      })
      .then(function(aSignedData) {
        append("getOut", "Signed Data assembled: " + hexEncode(aSignedData) + "\n");
        console.log(state.publicKey, aSignedData, aAssertion.response.signature);
        return verifySignature(state.publicKey, aSignedData, getArrayBuffer(aAssertion.response.signature));
      })
      .then(function(aSignatureValid) {
        test("getOut", aSignatureValid, "The token signature must be valid.");
      });
    }).catch(function (aErr) {
      if (aErr && (aErr.name == "AbortError" || aErr.name == "NS_ERROR_ABORT")) {
        gResults.reset();
        append("getOut", "Aborted; retry?\n");
      } else {
        gResults.fail();
        append("getOut", "Got error:\n");
        append("getOut", String(aErr) + "\n\n");
      }
    }).then(function (){
      append("getOut", "\n\nRaw request:\n");
      append("getOut", JSON.stringify(publicKeyCredentialRequestOptions, null, 2) + "\n\n");
    }).then(function (){
      resultColor("getOut");
      append("getOut", gResults.toString() + "\n\n");
    });

  });
});
