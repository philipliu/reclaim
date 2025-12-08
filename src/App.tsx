import { useState } from 'react'
import { startAuthentication, startRegistration } from '@simplewebauthn/browser'
import base64url from 'base64url'
import { Buffer } from 'buffer'
import {
  Address,
  BASE_FEE,
  Contract,
  Transaction,
  Keypair,
  TransactionBuilder,
  nativeToScVal,
  rpc,
  xdr,
  hash as stellarHash,
} from '@stellar/stellar-sdk'
import { AssembledTransaction } from '@stellar/stellar-sdk/contract'

if (!(window as any).Buffer) {
  ;(window as any).Buffer = Buffer
}

const DEFAULT_RPC = 'https://soroban-testnet.stellar.org'
const DEFAULT_NETWORK_PASSPHRASE = 'Test SDF Network ; September 2015'
const MIN_BASE_FEE = 2000 // Soroban RPC rejects fee-bumps below 2000 stroops

const hexToBytes = (hex: string) => Uint8Array.from(Buffer.from(hex, 'hex'))

const amountToI128 = (amount: string) => {
  const [wholeStr, fracStrRaw = ''] = amount.trim().split('.')
  if (!/^-?\d+$/.test(wholeStr || '0')) throw new Error('Amount must be numeric')
  if (fracStrRaw && !/^\d+$/.test(fracStrRaw)) throw new Error('Amount must be numeric')
  const negative = wholeStr.startsWith('-')
  const absWholeStr = negative ? wholeStr.slice(1) : wholeStr
  const whole = BigInt(absWholeStr || '0')
  const fracPadded = (fracStrRaw + '0000000').slice(0, 7)
  const frac = BigInt(fracPadded || '0')
  const scale = 10n ** 7n
  let val = whole * scale + frac
  if (negative) val = -val
  return val
}

const compactSignature = (signatureDER: Buffer): Buffer => {
  const CURVE_ORDER = BigInt('0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551')
  const HALF_CURVE_ORDER = CURVE_ORDER / 2n

  let offset = 2
  if (signatureDER[offset] !== 0x02) throw new Error('Invalid signature format')
  offset++
  const rLength = signatureDER[offset]
  offset++
  const r = BigInt('0x' + signatureDER.slice(offset, offset + rLength).toString('hex'))
  offset += rLength

  if (signatureDER[offset] !== 0x02) throw new Error('Invalid signature format')
  offset++
  const sLength = signatureDER[offset]
  offset++
  let s = BigInt('0x' + signatureDER.slice(offset, offset + sLength).toString('hex'))

  if (s > HALF_CURVE_ORDER) {
    s = CURVE_ORDER - s
  }

  const rBuf = Buffer.from(r.toString(16).padStart(64, '0'), 'hex')
  const sBuf = Buffer.from(s.toString(16).padStart(64, '0'), 'hex')
  return Buffer.concat([rBuf, sBuf])
}

const extractPublicKey = (response: any): string | null => {
  // Borrowed from reference implementation to pull uncompressed 65-byte pubkey
  const parse = (bytes: Uint8Array) =>
    Array.from(bytes)
      .map(b => b.toString(16).padStart(2, '0'))
      .join('')

  if (response.publicKey) {
    const buf = base64url.toBuffer(response.publicKey)
    if (buf.length >= 65 && buf[0] === 0x04) return parse(new Uint8Array(buf.slice(buf.length - 65)))
    for (let i = buf.length - 65; i >= 0; i--) {
      if (buf[i] === 0x04 && i + 65 <= buf.length) return parse(new Uint8Array(buf.slice(i, i + 65)))
    }
  }
  if (response.attestationObject) {
    const ao = base64url.toBuffer(response.attestationObject)
    for (let i = 0; i < ao.length - 70; i++) {
      if (
        ao[i] === 0x21 &&
        ao[i + 1] === 0x58 &&
        ao[i + 2] === 0x20 &&
        i + 35 < ao.length &&
        ao[i + 35] === 0x22 &&
        ao[i + 36] === 0x58 &&
        ao[i + 37] === 0x20
      ) {
        const x = ao.slice(i + 3, i + 35)
        const y = ao.slice(i + 38, i + 70)
        const pk = new Uint8Array(65)
        pk[0] = 0x04
        pk.set(x, 1)
        pk.set(y, 33)
        return parse(pk)
      }
    }
  }
  if (response.authenticatorData) {
    const ad = base64url.toBuffer(response.authenticatorData)
    if (ad.length > 37 && (ad[32] & 0x40)) {
      let offset = 37 + 16
      if (offset + 2 <= ad.length) {
        const credIdLen = (ad[offset] << 8) | ad[offset + 1]
        offset += 2 + credIdLen
        for (let i = offset; i < ad.length - 70 && i < offset + 200; i++) {
          if (
            ad[i] === 0x21 &&
            ad[i + 1] === 0x58 &&
            ad[i + 2] === 0x20 &&
            i + 35 < ad.length &&
            ad[i + 35] === 0x22 &&
            ad[i + 36] === 0x58 &&
            ad[i + 37] === 0x20
          ) {
            const x = ad.slice(i + 3, i + 35)
            const y = ad.slice(i + 38, i + 70)
            const pk = new Uint8Array(65)
            pk[0] = 0x04
            pk.set(x, 1)
            pk.set(y, 33)
            return parse(pk)
          }
        }
      }
    }
  }
  return null
}

function App() {
  const rpcUrl = (import.meta.env.VITE_RPC_URL as string | undefined) ?? DEFAULT_RPC
  const networkPassphrase =
    (import.meta.env.VITE_NETWORK_PASSPHRASE as string | undefined) ?? DEFAULT_NETWORK_PASSPHRASE
  const envContract = (import.meta.env.VITE_CONTRACT_ID as string | undefined) ?? ''
  const recoverySecret = (import.meta.env.VITE_RECOVERY_SECRET as string | undefined)?.trim() ?? ''
  const feePayerSecret =
    (import.meta.env.VITE_FEE_PAYER_SECRET as string | undefined)?.trim() ??
    (import.meta.env.VITE_TX_SOURCE_SECRET as string | undefined)?.trim() ??
    ''
  const recoveryCosignerSecret = (import.meta.env.VITE_RECOVERY_COSIGNER_SECRET as string | undefined)?.trim() ?? ''
  const tokenContractId = (import.meta.env.VITE_TOKEN_CONTRACT_ID as string | undefined)?.trim() ?? ''
  const rpId = (import.meta.env.VITE_RP_ID as string | undefined) ?? (window.location.hostname || 'localhost')

  const [contractId, setContractId] = useState(envContract)
  const [destination, setDestination] = useState('')
  const [amount, setAmount] = useState('1')

  const [passkeyHex, setPasskeyHex] = useState('')
  const [passkeyId, setPasskeyId] = useState('')

  const [busy, setBusy] = useState(false)
  const [balance, setBalance] = useState<string>('–')

  const logRotate = (msg: string) => console.log('[rotate]', msg)
  const logTransfer = (msg: string) => console.log('[transfer]', msg)

  const recoveryPub = recoverySecret ? Keypair.fromSecret(recoverySecret).publicKey() : ''
  const recoveryCosignerPub = recoveryCosignerSecret ? Keypair.fromSecret(recoveryCosignerSecret).publicKey() : ''
  const feePayerPub = feePayerSecret ? Keypair.fromSecret(feePayerSecret).publicKey() : recoveryPub
  const sourcePub = recoveryPub

  const fetchBalance = async () => {
    if (!contractId || !tokenContractId || !feePayerPub) {
      setBalance('—')
      return
    }
    try {
      const server = new rpc.Server(rpcUrl, { allowHttp: rpcUrl.startsWith('http://') })
      const sourceAccount = await server.getAccount(feePayerPub)
      const op = new Contract(tokenContractId.trim()).call(
        'balance',
        Address.fromString(contractId.trim()).toScVal()
      )
      const tx = new TransactionBuilder(sourceAccount, {
        fee: BASE_FEE,
        networkPassphrase,
      })
        .addOperation(op)
        .setTimeout(30)
        .build()
      const sim = await server.simulateTransaction(tx)
      const scv = 'result' in sim ? sim.result?.retval : undefined
      if (scv && scv.switch().name === 'scvI128') {
        const hi = BigInt(scv.i128().hi().toString())
        const lo = BigInt(scv.i128().lo().toString())
        const val = (hi << 64n) + lo
        const scale = 10n ** 7n
        const whole = val / scale
        const frac = val % scale
        const display =
          frac === 0n
            ? whole.toString()
            : `${whole.toString()}.${frac.toString().padStart(7, '0').replace(/0+$/, '')}`
        setBalance(display)
        setAmount(display)
        logRotate(`Balance simulation: ${display}`)
      } else {
        setBalance('n/a')
        logRotate('Balance simulation returned no result')
      }
    } catch (err: any) {
      console.error(err)
      setBalance('error')
      logRotate(`Balance check failed: ${err.message || err}`)
    }
  }

  const ensureFeePayer = () => {
    const secret = feePayerSecret.trim() || recoverySecret.trim()
    if (!secret) throw new Error('Configure VITE_FEE_PAYER_SECRET (or VITE_TX_SOURCE_SECRET) or VITE_RECOVERY_SECRET in .env')
    return Keypair.fromSecret(secret)
  }

  const feeBumpSigner =
    (signer: Keypair, _server: rpc.Server, baseFee: string = MIN_BASE_FEE.toString()) =>
    async (xdrStr: string) => {
      let tx = TransactionBuilder.fromXDR(xdrStr, networkPassphrase) as Transaction
      // ensure inner tx is signed by fee payer (in addition to auth entries)
      tx.sign(signer)
      let feeBump = TransactionBuilder.buildFeeBumpTransaction(signer, baseFee, tx, networkPassphrase)
      feeBump.sign(signer)
      return { signedTxXdr: feeBump.toXDR(), signerAddress: signer.publicKey() }
    }

  const waitForTx = async (server: rpc.Server, hash: string, timeoutMs = 15000, intervalMs = 1000) => {
    const start = Date.now()
    let lastStatus = 'PENDING'
    while (Date.now() - start < timeoutMs) {
      const res = await server.getTransaction(hash).catch(() => undefined)
      if (res && res.status !== rpc.Api.GetTransactionStatus.NOT_FOUND) {
        return res
      }
      lastStatus = res?.status ?? 'NOT_FOUND'
      await new Promise(r => setTimeout(r, intervalMs))
    }
    return { status: lastStatus }
  }

  const createPasskey = async () => {
    setBusy(true)
    try {
      // Passkey creation uses browser prompts; logs go to console in later steps
      const challengeBytes = new Uint8Array(32)
      crypto.getRandomValues(challengeBytes)
      const challenge = base64url(Buffer.from(challengeBytes))

      const raw = await startRegistration({
        optionsJSON: {
          challenge,
          rp: { id: rpId, name: 'Smart Wallet Rescue' },
          user: {
            id: base64url(Buffer.from(`user-${Date.now()}`)),
            name: contractId || 'smart-wallet-user',
            displayName: contractId || 'Smart Wallet User',
          },
          pubKeyCredParams: [{ alg: -7, type: 'public-key' }],
          authenticatorSelection: { residentKey: 'preferred', userVerification: 'required' },
        },
      })

      const hex = extractPublicKey(raw.response)
      if (!hex) throw new Error('Could not extract public key')
      setPasskeyHex(hex)
      setPasskeyId(raw.id)
      // minimal UI: no dedicated passkey log
    } catch (err: any) {
      console.error(err)
      // minimal UI: surface in console only
    } finally {
      setBusy(false)
    }
  }


  const rotateSigner = async () => {
    if (!contractId || !recoverySecret || !recoveryCosignerSecret || !passkeyHex) {
      logRotate('Fill contract id, create a passkey, and ensure recovery + recovery cosigner + fee payer secrets are set in .env.')
      return
    }
    setBusy(true)
    try {
      const server = new rpc.Server(rpcUrl, { allowHttp: rpcUrl.startsWith('http://') })
      const recovery = Keypair.fromSecret(recoverySecret.trim())
      const recoveryCosigner = Keypair.fromSecret(recoveryCosignerSecret.trim())

      // For rotate_signer, the contract's require_auth checks the stored recovery address (ed25519 G-address).
      // Use the recovery account as the transaction source to satisfy require_auth.
      const sourceAccount = recovery.publicKey()
      const account = await server.getAccount(sourceAccount)

      const signerBytes = hexToBytes(passkeyHex)
      const contract = new Contract(contractId.trim())
      let txBuilder = new TransactionBuilder(account, {
        fee: Math.max(Number(BASE_FEE) * 20, MIN_BASE_FEE).toString(),
        networkPassphrase,
      })
        .addOperation(contract.call('rotate_signer', nativeToScVal(signerBytes, { type: 'bytes' })))
        .setTimeout(60)
      let tx = txBuilder.build()

      tx = await server.prepareTransaction(tx)
      // 2/2 multisig signatures required
      tx.sign(recovery) // source == recovery
      tx.sign(recoveryCosigner)

      // Fee bump with fee payer
      const feePayer = ensureFeePayer()
      // build fee bump without re-prepare to keep inner Soroban data intact
      const feeBump = TransactionBuilder.buildFeeBumpTransaction(
        feePayer,
        MIN_BASE_FEE.toString(),
        tx,
        networkPassphrase
      )
      feeBump.sign(feePayer)

      const xdrBase64 = feeBump.toXDR()
      logRotate(`rotate_signer fee bump tx XDR (base64): ${xdrBase64}`)

      const sent = await server.sendTransaction(feeBump)
      logRotate(`rotate_signer submitted. Hash: ${sent.hash} status: ${sent.status}`)

      const final = await waitForTx(server, sent.hash)
      logRotate(`rotate_signer status: ${final.status}`)
    } catch (err: any) {
      console.error(err)
      logRotate(`rotate_signer failed: ${err.message || err}`)
    } finally {
      setBusy(false)
    }
  }

  const transferFunds = async () => {
    if (!contractId || !tokenContractId || !destination) {
      logTransfer('Fill contract id, destination, amount (UI) and ensure secrets are set in .env.')
      return
    }
    setBusy(true)
    try {
      const payer = ensureFeePayer()
      const transferAmount = amountToI128(amount)
      const op = new Contract(tokenContractId.trim()).call(
        'transfer',
        Address.fromString(contractId.trim()).toScVal(),
        Address.fromString(destination.trim()).toScVal(),
        nativeToScVal(transferAmount, { type: 'i128' })
      )

      const assembled = await AssembledTransaction.buildWithOp(op, {
        method: 'transfer',
        contractId: tokenContractId.trim(),
        networkPassphrase,
        rpcUrl,
        allowHttp: rpcUrl.startsWith('http://'),
        publicKey: payer.publicKey(),
        parseResultXdr: () => undefined,
        fee: (Number(BASE_FEE) * 20).toString(),
      })

      const signAuthEntry = async (entry: xdr.SorobanAuthorizationEntry) => {
        const addressCredentials = entry.credentials().address()
        const latest = await new rpc.Server(rpcUrl, { allowHttp: rpcUrl.startsWith('http://') }).getLatestLedger()
        const expiration = latest.sequence + 10
        addressCredentials.signatureExpirationLedger(expiration)

        const nonceVal = addressCredentials.nonce()
        const nonceBig = typeof nonceVal === 'bigint' ? nonceVal : BigInt(nonceVal.toString())

        const preimage = xdr.HashIdPreimage.envelopeTypeSorobanAuthorization(
          new xdr.HashIdPreimageSorobanAuthorization({
            networkId: stellarHash(Buffer.from(networkPassphrase)),
            nonce: xdr.Int64.fromString(nonceBig.toString()),
            signatureExpirationLedger: expiration,
            invocation: entry.rootInvocation(),
          })
        )
        const payload = stellarHash(preimage.toXDR())
        const challenge = base64url(payload)

      if (!passkeyId) throw new Error('Create a passkey first')
      const authentication = await startAuthentication({
        optionsJSON: {
          challenge,
          rpId,
          allowCredentials: [{ id: passkeyId, type: 'public-key' }],
          userVerification: 'required',
        },
      })

      setPasskeyId(authentication.id)

      const signature = compactSignature(Buffer.from(base64url.toBuffer(authentication.response.signature)))
        const webAuthnCredential = xdr.ScVal.scvMap([
          new xdr.ScMapEntry({
            key: xdr.ScVal.scvSymbol('authenticator_data'),
            val: xdr.ScVal.scvBytes(Buffer.from(base64url.toBuffer(authentication.response.authenticatorData))),
          }),
          new xdr.ScMapEntry({
            key: xdr.ScVal.scvSymbol('client_data_json'),
            val: xdr.ScVal.scvBytes(Buffer.from(base64url.toBuffer(authentication.response.clientDataJSON))),
          }),
          new xdr.ScMapEntry({
            key: xdr.ScVal.scvSymbol('signature'),
            val: xdr.ScVal.scvBytes(signature),
          }),
        ])

        addressCredentials.signature(webAuthnCredential)
        return entry
      }

      await assembled.signAuthEntries({
        address: contractId.trim(),
        authorizeEntry: signAuthEntry,
      })

      await assembled.simulate()
      const simData: any = assembled.simulation
      const innerFee = Number(assembled.options.fee || MIN_BASE_FEE)
      const simMinFee =
        simData?.minResourceFee ??
        simData?.transactionData?.minResourceFee ??
        simData?.resourceFee ??
        MIN_BASE_FEE
      const feeBumpBase = Math.max(Number(simMinFee), innerFee, MIN_BASE_FEE, 300000)

      const server = new rpc.Server(rpcUrl, { allowHttp: rpcUrl.startsWith('http://') })
      const sent = await assembled.signAndSend({
        signTransaction: feeBumpSigner(payer, server, feeBumpBase.toString()) as any,
      })

      const hash = sent.sendTransactionResponse?.hash
      logTransfer(`Transfer submitted. Hash: ${hash ?? 'unknown'}`)
      const status = sent.getTransactionResponse?.status ?? 'PENDING'
      logTransfer(`Transfer status: ${status}`)
    } catch (err: any) {
      console.error(err)
      logTransfer(`Transfer failed: ${err.message || err}`)
    } finally {
      setBusy(false)
    }
  }

  return (
    <div style={{ display: 'flex', flexDirection: 'column', gap: 12 }}>
      <div>
        <div>Contract Address</div>
        <input value={contractId} onChange={e => setContractId(e.target.value)} placeholder="C..." />
      </div>

      <div>
        <button disabled={busy || !contractId} onClick={fetchBalance}>Check balance</button>
        <div>Balance: {balance}</div>
      </div>

      <div>
        <button disabled={busy} onClick={createPasskey}>Create passkey</button>
        {passkeyHex && (
          <div>
            credentialId: {passkeyId}
            <br />pubkey (hex): {passkeyHex}
          </div>
        )}
      </div>

      <div>
        <button disabled={busy || !passkeyHex} onClick={rotateSigner}>rotate_signer</button>
      </div>

      <div>
        <div>Destination (G... or C...)</div>
        <input value={destination} onChange={e => setDestination(e.target.value)} />
        <div>Amount</div>
        <input value={amount} onChange={e => setAmount(e.target.value)} />
      </div>
      <div>
        <button disabled={busy || !passkeyHex} onClick={transferFunds}>Transfer</button>
      </div>
    </div>
  )
}

export default App
