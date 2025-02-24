# key encapsulation mechanism
using Random: RandomDevice
using CryptoGroups: Group
using SigmaProofs.Parser: encode, decode
import Nettle

abstract type EncryptSpec end

EncryptSpec(spec::Symbol) = EncryptSpec(Val(spec))::EncryptSpec

struct PlaintextMode <: EncryptSpec end
EncryptSpec(::Val{:PlaintextMode}) = PlaintextMode()

encrypt(plaintext::Vector{UInt8}, key::Vector{UInt8}, ::PlaintextMode) = plaintext
decrypt(ciphertext::Vector{UInt8}, key::Vector{UInt8}, ::PlaintextMode) = ciphertext

struct AES256_SHA256 <: EncryptSpec end
EncryptSpec(::Val{:AES256_SHA256}) = AES256_SHA256()

function encrypt(plaintext::Vector{UInt8}, key::Vector{UInt8}, ::AES256_SHA256)
   
    hashed_key = Nettle.digest("sha256", key)
    padded_plaintext = Nettle.add_padding_PKCS5(plaintext, 16)

    return Nettle.encrypt("AES256", hashed_key, padded_plaintext)
end

function decrypt(ciphertext::Vector{UInt8}, key::Vector{UInt8}, ::AES256_SHA256)

    hashed_key = Nettle.digest("sha256", key)
    padded_plaintext = Nettle.decrypt("AES256", hashed_key, ciphertext)

    return Nettle.trim_padding_PKCS5(padded_plaintext)
end

struct Encap{G}
    k::Vector{UInt8}
    c::G
end

function encap(g::G, y::G; r = rand(RandomDevice(), 2:order(G) - 1)) where G <: Group

    t = y^r
    k = octet(t) # further hashing recomended
    c = g^r

    return Encap(k, c)
end

function decap(c::Group, sk::Integer)

    t = c^sk
    k = octet(t)

    return k
end

decap(encap::Encap) = encap.k

struct Encryption{T, G}
    encapsulation::G
    ciphertext::Vector{UInt8}
end

function encrypt(msg::T, kc::Encap{G}, spec::EncryptSpec) where {T, G <: Group}
    
    plaintext = encode(Tree(msg))
    
    ciphertext = encrypt(plaintext, kc.k, spec)

    return Encryption{T, G}(kc.c, ciphertext)
end

encrypt(msg::T, g::G, pk::G, spec::EncryptSpec) where {T, G <: Group} = encrypt(msg, encap(g, pk), spec)

function decrypt(msg::Encryption{T, G}, sk::Integer, spec::EncryptSpec; key = decap(msg.encapsulation, sk)) where {T, G <: Group}

    ciphertext = msg.ciphertext

    plaintext = decrypt(ciphertext, key, spec)

    tree = decode(plaintext)

    return convert(T, tree)
end
