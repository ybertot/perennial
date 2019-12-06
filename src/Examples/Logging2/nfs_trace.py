## mount localhost:/ /mnt/x -o vers=3
## tcpdump -w /tmp/nfs.pcap -s 1600 -i lo port 2049 
## git clone -b python2 https://github.com/hawk78/pyrpcgen.git

import dpkt
import struct
import xdrlib
import rfc1057
import rfc1813

def unpack_call(proc, nextdata):
  unpacker = rfc1813.pack.protUnpacker(nextdata)
  if proc == 3: #lookup
    return unpacker.unpack_LOOKUP3args()
  elif proc == 4: #access
    return unpacker.unpack_ACCESS3args()
  else:
    raise Exception("unpack_call:", proc)

def unpack_reply(proc, nextdata):
  unpacker = rfc1813.pack.protUnpacker(nextdata)
  if proc == 3: #lookup
    return unpacker.unpack_LOOKUP3res()
  elif proc == 4: #access
    return unpacker.unpack_ACCESS3res()
  else:
    raise Exception("unpack_call:", proc)

pending_calls = {}

with open('/tmp/nfs.pcap') as f:
  for ts, pkt in dpkt.pcap.Reader(f):
    eth = dpkt.ethernet.Ethernet(pkt)
    if eth.type != dpkt.ethernet.ETH_TYPE_IP:
      continue

    ip = eth.data
    if ip.p != dpkt.ip.IP_PROTO_TCP:
      continue

    tcp = ip.tcp
    data = tcp.data
    if len(data) < 4:
      continue

    (hdr,) = struct.unpack("!L", data[0:4])
    hdrfinal = (hdr & 0x80000000) != 0
    hdrlen = hdr & 0x7fffffff
    if not hdrfinal:
      raise Exception("fragmented RPC not supported")

    xdrdata = data[4:]
    if len(xdrdata) != hdrlen:
      raise Exception("partial TCP data")

    rfc1057unpacker = rfc1057.pack.protUnpacker(xdrdata)
    rpc_msg = rfc1057unpacker.unpack_rpc_msg()
    xid = rpc_msg.xid
    body = rpc_msg.body

    nextdata = xdrdata[rfc1057unpacker.get_position():]

    if body.mtype == rfc1057.const.CALL:
      proc_args = unpack_call(body.cbody.proc, nextdata)
      pending_calls[xid] = (body.cbody, proc_args)
      continue

    if body.rbody.stat != rfc1057.const.MSG_ACCEPTED:
      continue

    areply = body.rbody.areply
    if areply.reply_data.stat != rfc1057.const.SUCCESS:
      continue

    (cbody, proc_args) = pending_calls[xid]
    proc_reply = unpack_reply(cbody.proc, nextdata)

    print "proc", cbody.proc, "args", proc_args, "reply", proc_reply
