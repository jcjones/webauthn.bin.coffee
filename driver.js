var TIMEOUT = 2000; // ms

function append(id, text) {
  $("#"+id).text($("#"+id).text() + text);
}

function test(id, test, text) {
  let message = (test)? "[PASS]" : "[FAIL]";
  message += " " + text + "\n";
  append(id, message);
  return test;
}

function testEqual(id, val1, val2) {
  let result = (val1 == val2);
  let cmp = (result)? " == " : " != ";
  return test(id, result, "" + val1 + cmp + val2);
}

function resultColor(id, success) {
  if (success) { $("#"+id).removeClass("failure"); $("#"+id).addClass("success"); }
  else         { $("#"+id).removeClass("success"); $("#"+id).addClass("failure"); }
}

function hexEncode(buf) {
  return Array.from(buf)
              .map(function(x){ return ("0"+x.toString(16)).substr(-2) })
              .join("");
}

function hexDecode(str) {
  return new Uint8Array(str.match(/../g).map(function(x){ return parseInt(x, 16) }));
}

function b64enc(buf) {
  return base64js.fromByteArray(buf)
                 .replace(/\+/g, "-")
                 .replace(/\//g, "_")
                 .replace(/=/g, "");
}

function string2buffer(str) {
  return (new Uint8Array(str.length)).map(function(x, i){ return str.charCodeAt(i) });
}

function buffer2string(buf) {
  let str = "";
  buf.map(function(x){ return str += String.fromCharCode(x) });
  return str;
}

function b64dec(str) {
  if (str.length % 4 == 1) {
    throw "Improper b64 string";
  }

  var b64 = str;
  while (b64.length % 4 != 0) {
    b64 += "=";
  }
  return new Uint8Array(base64js.toByteArray(b64));
}

function deriveAppAndChallengeParam(appId, clientData) {
  console.log(appId.toString());
  var appIdBuf = string2buffer(appId.toString());
  return Promise.all([
    crypto.subtle.digest("SHA-256", appIdBuf),
    crypto.subtle.digest("SHA-256", clientData)
  ])
  .then(function(digests) {
    return {
      appParam: new Uint8Array(digests[0]),
      challengeParam: new Uint8Array(digests[1]),
    };
  });
}

function assembleSignedData(appParam, presenceAndCounter, challengeParam) {
  let signedData = new Uint8Array(32 + 1 + 4 + 32);
  appParam.map((x, i) => signedData[0 + i] = x);
  presenceAndCounter.map((x, i) => signedData[32 + i] = x);
  challengeParam.map((x, i) => signedData[37 + i] = x);
  return signedData;
}

function assembleRegistrationSignedData(appParam, challengeParam, keyHandle, pubKey) {
  let signedData = new Uint8Array(1 + 32 + 32 + keyHandle.length + 65);
  signedData[0] = 0x00;
  appParam.map((x, i) => signedData[1 + i] = x);
  challengeParam.map((x, i) => signedData[33 + i] = x);
  keyHandle.map((x, i) => signedData[65 + i] = x);
  pubKey.map((x, i) => signedData[65 + keyHandle.length + i] = x);
  return signedData;
}


var state = {
  // Raw messages
  createRequest: null,
  createResponse: null,
  // challengeBytes: null,
  // registeredKey: null,
  // signResponse: null,

  // Parsed values
  publicKey: null,
  keyHandle: null,
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

function verifySignature(key, data, derSig) {
  if (derSig.byteLength < 70) {
    console.log("bad sig: " + hexEncode(derSig))
    throw "Invalid signature length: " + derSig.byteLength;
  }

  // Poor man's ASN.1 decode
  // R and S are always 32 bytes.  If ether has a DER
  // length > 32, it's just zeros we can chop off.
  var lenR = derSig[3];
  var lenS = derSig[3 + lenR + 2];
  var padR = lenR - 32;
  var padS = lenS - 32;
  var sig = new Uint8Array(64);
  derSig.subarray(4+padR,4+lenR).map(function(x,i) { return sig[i] = x });
  derSig.subarray(4+lenR+2+padS,4+lenR+2+lenS).map(function(x,i) { return sig[32+i] = x });

  console.log("data: " + hexEncode(data));
  console.log("der:  " + hexEncode(derSig));
  console.log("raw:  " + hexEncode(sig));

  let asn1 = org.pkijs.fromBER(derSig);

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



$(document).ready(function() {
  if (!PublicKeyCredential) {
    $("#error").text("Web Authentication API not found");
    $("button").addClass("inactive");
  }

  state.version = "U2F_V2";

  let success = true;

  $("#createButton").click(function() {
    $("#createOut").text("");

    let challengeBytes = new Uint8Array(16);
    window.crypto.getRandomValues(challengeBytes);

    let createRequest = {
      challenge: challengeBytes,
      // Relying Party:
      rp: {
        id: $("#rpIdText").val(),
        name: "Acme"
      },

      // User:
      user: {
        id: "1098237235409872",
        name: "john.p.smith@example.com",
        displayName: "John P. Smith",
        icon: "https://pics.acme.com/00/p/aBjjjpqPb.png"
      },

      parameters: [
        {
          type: "public-key",
          algorithm: "p-256", // Not actually in-spec, but TODO in Firefox
        },
        {
          type: "public-key",
          algorithm: "ES256",
        }
      ],

      timeout: 60000,  // 1 minute
      excludeList: [] // No excludeList
    };
    state.createRequest = createRequest;

    append("createOut", "Sending request:\n");
    append("createOut", JSON.stringify(createRequest, null, 2) + "\n\n");

    navigator.credentials.create({ publicKey: createRequest })
    .then(function (aNewCredentialInfo) {
      state.createResponse = aNewCredentialInfo
      append("createOut", "Raw response in console.\n");
      console.log("Credentials.Create response: ", aNewCredentialInfo);

      if (!testEqual("createOut", aNewCredentialInfo.response.attestationObject[0], 0x05)) {
        throw "Attestation Object's header byte is incorrect";
      }

      let clientData = JSON.parse(buffer2string(aNewCredentialInfo.response.clientDataJSON));
      append("createOut", "Client Data:\n");
      append("createOut", JSON.stringify(clientData, null, 2) + "\n\n");

      testEqual("createOut", b64enc(challengeBytes), clientData.challenge);
      testEqual("createOut", window.location.origin, clientData.origin);
      if (clientData.hashAlg) {
        // TODO: Remove this check - Spec changed
        testEqual("createOut", "S256", clientData.hashAlg);
        append("createOut", "NOTE: Using WD-05 hashAlg name, not WD-06 hashAlgorithm\n");
      } else if (clientData.hashAlgorithm) {
        testEqual("createOut", "SHA-256", clientData.hashAlgorithm);
      } else {
        throw "Unknown spec version: Missing clientData.hashAlgorithm";
      }

      let u2fObj = aNewCredentialInfo.response.attestationObject;

      state.publicKeyBytes = u2fObj.subarray(1, 66);
      let keyHandleLength = u2fObj[66];
      state.keyHandle = b64enc(u2fObj.subarray(67, 67 + keyHandleLength));
      state.attestation = new Uint8Array(u2fObj.subarray(67 + keyHandleLength));

      append("createOut", "Key Handle: " + hexEncode(state.keyHandle) + "\n");
      append("createOut", "Certificate: " + hexEncode(state.attestation) + "\n");

      let certAsn1 = org.pkijs.fromBER(state.attestation.buffer);
      if (!test("createOut", asn1Okay(certAsn1), "Attestation Certificate is OK")) {
        throw "Attestation Certificate didn't parse correctly.";
      }

      state.attestationSig = new Uint8Array(state.attestation.slice(certAsn1.offset));
      state.attestationCert = new org.pkijs.simpl.CERT({ schema: certAsn1.result });
      append("createOut", "Attestation Cert\n");
      append("createOut", "Subject: " + state.attestationCert.subject.types_and_values[0].value.value_block.value + "\n");
      append("createOut", "Issuer: " + state.attestationCert.issuer.types_and_values[0].value.value_block.value + "\n");
      append("createOut", "Validity (in millis): " + (state.attestationCert.notAfter.value - state.attestationCert.notBefore.value + "\n"));

      let sigAsn1 = org.pkijs.fromBER(state.attestationSig.buffer);
      if (!test("createOut", asn1Okay(certAsn1), "Attestation Signature is OK")) {
        throw "Attestation Signature failed to validate";
      }

      append("createOut", "Attestation Signature\n");
      let R = new Uint8Array(sigAsn1.result.value_block.value[0].value_block.value_hex);
      let S = new Uint8Array(sigAsn1.result.value_block.value[1].value_block.value_hex);
      append("createOut", "R: " + hexEncode(R) + "\n");
      append("createOut", "S: " + hexEncode(S) + "\n");

      // Import the public key
      importPublicKey(state.publicKeyBytes)
      .then(function(aKey) {
        state.publicKey = aKey;
        success = test("createOut", true, "Imported public key");
        resultColor("createOut", success);
      })
      .catch(function(aErr) {
        console.log("Credentials.Create: Error importing key ", aErr);
        throw "Error Importing Key: " + err;
      });

    }).catch(function (aErr) {
      resultColor("createOut", false);
      append("createOut", "Got error:\n");
      append("createOut", aErr.toString() + "\n\n");
      return;
    });

  });

  $("#getButton").click(function() {
    $("#getOut").text("");

    if (!state.createResponse) {
      resultColor("getOut", false);
      append("getOut", "Need to make a credential first:\n");
      return;
    }

    let newCredential = {
      type: "public-key",
      id: Uint8Array.from(state.createResponse.rawId),
      transports: ["usb", "nfc", "ble"],
    }

    let challengeBytes = new Uint8Array(16);
    window.crypto.getRandomValues(challengeBytes);

    let publicKeyCredentialRequestOptions = {
      challenge: challengeBytes,
      timeout: 60000,
      rpId: $("#rpIdText").val(),
      allowList: [newCredential]
    };

    navigator.credentials.get({publicKey: publicKeyCredentialRequestOptions})
    .then(function(aAssertion) {
      console.log("Credentials.Get response: ", aAssertion);
      append("getOut", "Raw response in console.\n");

      let clientData = JSON.parse(buffer2string(aAssertion.response.clientDataJSON));
      testEqual("getOut", clientData.challenge, b64enc(challengeBytes));
      testEqual("getOut", clientData.origin, window.location.origin);
      if (clientData.hashAlg) {
        // TODO: Remove this check - Spec changed
        testEqual("getOut", "S256", clientData.hashAlg);
        append("getOut", "NOTE: Using WD-05 hashAlg name, not WD-06 hashAlgorithm\n");
      } else if (clientData.hashAlgorithm) {
        testEqual("getOut", "SHA-256", clientData.hashAlgorithm);
      } else {
        throw "Unknown spec version: Missing clientData.hashAlgorithm";
      }

      if (!testEqual("getOut", aAssertion.response.signature[0], 0x01)) {
        throw "Assertion's user presence byte not set correctly.";
      }

      let presenceAndCounter = aAssertion.response.signature.slice(0,5);
      let signatureValue = aAssertion.response.signature.slice(5);
      let rpIdHash = aAssertion.response.authenticatorData.slice(0,32);

      // Assemble the signed data and verify the signature
      return deriveAppAndChallengeParam(clientData.origin, aAssertion.response.clientDataJSON)
      .then(function(aParams) {
        console.log(aParams.appParam, rpIdHash, presenceAndCounter, aParams.challengeParam);
        append("getOut", "ClientData buffer: " + hexEncode(aAssertion.response.clientDataJSON) + "\n\n");
        append("getOut", "ClientDataHash: " + hexEncode(aParams.challengeParam) + "\n\n");
        return assembleSignedData(aParams.appParam, presenceAndCounter, aParams.challengeParam);
      })
      .then(function(aSignedData) {
        append("getOut", "Signed Data assembled: " + aSignedData + "\n");
        console.log(state.publicKey, aSignedData, signatureValue);
        return verifySignature(state.publicKey, aSignedData, signatureValue);
      })
      .then(function(aSignatureValid) {
        test("getOut", aSignatureValid, "The token signature must be valid.");
        resultColor("getOut", aSignatureValid);
      });

    }).catch(function (aErr) {
      resultColor("getOut", false);
      append("getOut", "Got error:\n");
      append("getOut", aErr.toString() + "\n\n");
      return;
    });
  });
});
