

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 217) then
					if (Enum <= 108) then
						if (Enum <= 53) then
							if (Enum <= 26) then
								if (Enum <= 12) then
									if (Enum <= 5) then
										if (Enum <= 2) then
											if (Enum <= 0) then
												local A;
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A](Unpack(Stk, A + 1, Inst[3]));
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]];
											elseif (Enum > 1) then
												Upvalues[Inst[3]] = Stk[Inst[2]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Upvalues[Inst[3]] = Stk[Inst[2]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Upvalues[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Upvalues[Inst[3]] = Stk[Inst[2]];
											else
												local Results;
												local Edx;
												local Results, Limit;
												local B;
												local A;
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												B = Stk[Inst[3]];
												Stk[A + 1] = B;
												Stk[A] = B[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												B = Stk[Inst[3]];
												Stk[A + 1] = B;
												Stk[A] = B[Inst[4]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Results, Limit = _R(Stk[A](Stk[A + 1]));
												Top = (Limit + A) - 1;
												Edx = 0;
												for Idx = A, Top do
													Edx = Edx + 1;
													Stk[Idx] = Results[Edx];
												end
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Results = {Stk[A](Unpack(Stk, A + 1, Top))};
												Edx = 0;
												for Idx = A, Inst[4] do
													Edx = Edx + 1;
													Stk[Idx] = Results[Edx];
												end
												VIP = VIP + 1;
												Inst = Instr[VIP];
												VIP = Inst[3];
											end
										elseif (Enum <= 3) then
											local A;
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										elseif (Enum > 4) then
											local B;
											local T;
											local A;
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											T = Stk[A];
											B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										else
											local A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										end
									elseif (Enum <= 8) then
										if (Enum <= 6) then
											local K;
											local B;
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										elseif (Enum == 7) then
											local B;
											local T;
											local A;
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											T = Stk[A];
											B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 10) then
										if (Enum == 9) then
											local K;
											local B;
											local Edx;
											local Results;
											local A;
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Results = {Stk[A](Stk[A + 1])};
											Edx = 0;
											for Idx = A, Inst[4] do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = #Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										else
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
										end
									elseif (Enum == 11) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] < Stk[Inst[4]]) then
											VIP = Inst[3];
										else
											VIP = VIP + 1;
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 19) then
									if (Enum <= 15) then
										if (Enum <= 13) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Enum > 14) then
											local A = Inst[2];
											local Cls = {};
											for Idx = 1, #Lupvals do
												local List = Lupvals[Idx];
												for Idz = 0, #List do
													local Upv = List[Idz];
													local NStk = Upv[1];
													local DIP = Upv[2];
													if ((NStk == Stk) and (DIP >= A)) then
														Cls[DIP] = NStk[DIP];
														Upv[1] = Cls;
													end
												end
											end
										else
											local A;
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
										end
									elseif (Enum <= 17) then
										if (Enum == 16) then
											local B;
											local T;
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											T = Stk[A];
											B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										else
											local A;
											local K;
											local B;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										end
									elseif (Enum == 18) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									else
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									end
								elseif (Enum <= 22) then
									if (Enum <= 20) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 21) then
										Stk[Inst[2]] = Inst[3];
									else
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 24) then
									if (Enum == 23) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local Results;
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum == 25) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 39) then
								if (Enum <= 32) then
									if (Enum <= 29) then
										if (Enum <= 27) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = #Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
										elseif (Enum > 28) then
											local A;
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										else
											local B;
											local T;
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											T = Stk[A];
											B = Inst[3];
											for Idx = 1, B do
												T[Idx] = Stk[A + Idx];
											end
										end
									elseif (Enum <= 30) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									elseif (Enum == 31) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] < Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 35) then
									if (Enum <= 33) then
										local B = Stk[Inst[4]];
										if B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									elseif (Enum == 34) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									else
										local K;
										local B;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 37) then
									if (Enum == 36) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum > 38) then
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 46) then
								if (Enum <= 42) then
									if (Enum <= 40) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									elseif (Enum == 41) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
									end
								elseif (Enum <= 44) then
									if (Enum > 43) then
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									else
										local A = Inst[2];
										local C = Inst[4];
										local CB = A + 2;
										local Result = {Stk[A](Stk[A + 1], Stk[CB])};
										for Idx = 1, C do
											Stk[CB + Idx] = Result[Idx];
										end
										local R = Result[1];
										if R then
											Stk[CB] = R;
											VIP = Inst[3];
										else
											VIP = VIP + 1;
										end
									end
								elseif (Enum > 45) then
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 49) then
								if (Enum <= 47) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum == 48) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B;
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum <= 51) then
								if (Enum > 50) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum == 52) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 80) then
							if (Enum <= 66) then
								if (Enum <= 59) then
									if (Enum <= 56) then
										if (Enum <= 54) then
											local A = Inst[2];
											do
												return Stk[A], Stk[A + 1];
											end
										elseif (Enum == 55) then
											local A;
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										end
									elseif (Enum <= 57) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									elseif (Enum == 58) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									end
								elseif (Enum <= 62) then
									if (Enum <= 60) then
										local Step;
										local Index;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Index = Stk[A];
										Step = Stk[A + 2];
										if (Step > 0) then
											if (Index > Stk[A + 1]) then
												VIP = Inst[3];
											else
												Stk[A + 3] = Index;
											end
										elseif (Index < Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Enum > 61) then
										local A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Top));
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 64) then
									if (Enum > 63) then
										local A;
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
									end
								elseif (Enum == 65) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local Edx;
									local Results;
									local A;
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 73) then
								if (Enum <= 69) then
									if (Enum <= 67) then
										local A = Inst[2];
										local T = Stk[A];
										for Idx = A + 1, Top do
											Insert(T, Stk[Idx]);
										end
									elseif (Enum == 68) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									else
										local A;
										local K;
										local B;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									end
								elseif (Enum <= 71) then
									if (Enum == 70) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										local K;
										local B;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum == 72) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 76) then
								if (Enum <= 74) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								elseif (Enum == 75) then
									local Step;
									local Index;
									local A;
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Index = Stk[A];
									Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 78) then
								if (Enum == 77) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
								else
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum > 79) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 94) then
							if (Enum <= 87) then
								if (Enum <= 83) then
									if (Enum <= 81) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum == 82) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 85) then
									if (Enum > 84) then
										local DIP;
										local NStk;
										local Upv;
										local List;
										local Cls;
										local A;
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Cls = {};
										for Idx = 1, #Lupvals do
											List = Lupvals[Idx];
											for Idz = 0, #List do
												Upv = List[Idz];
												NStk = Upv[1];
												DIP = Upv[2];
												if ((NStk == Stk) and (DIP >= A)) then
													Cls[DIP] = NStk[DIP];
													Upv[1] = Cls;
												end
											end
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
									else
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum > 86) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 90) then
								if (Enum <= 88) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 89) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 92) then
								if (Enum == 91) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum > 93) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 101) then
							if (Enum <= 97) then
								if (Enum <= 95) then
									local B;
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								elseif (Enum > 96) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								end
							elseif (Enum <= 99) then
								if (Enum > 98) then
									local A = Inst[2];
									local Index = Stk[A];
									local Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum > 100) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 104) then
							if (Enum <= 102) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 103) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 106) then
							if (Enum == 105) then
								local Results, Limit;
								local Edx;
								local Results;
								local A;
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum == 107) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Inst[2] > Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 162) then
						if (Enum <= 135) then
							if (Enum <= 121) then
								if (Enum <= 114) then
									if (Enum <= 111) then
										if (Enum <= 109) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
										elseif (Enum == 110) then
											local A;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if (Stk[Inst[2]] == Inst[4]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 112) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									elseif (Enum == 113) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] <= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] < Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 117) then
									if (Enum <= 115) then
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									elseif (Enum > 116) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local A;
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 119) then
									if (Enum > 118) then
										local K;
										local B;
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									else
										local A = Inst[2];
										local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
										local Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									end
								elseif (Enum == 120) then
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 128) then
								if (Enum <= 124) then
									if (Enum <= 122) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
									elseif (Enum > 123) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum <= 126) then
									if (Enum == 125) then
										local B;
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Stk[Inst[4]];
										if B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									else
										local Results;
										local Edx;
										local Results, Limit;
										local B;
										local A;
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Unpack(Stk, A + 1, Top))};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum > 127) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local B;
									local T;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 131) then
								if (Enum <= 129) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								elseif (Enum > 130) then
									local DIP;
									local NStk;
									local Upv;
									local List;
									local Cls;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Cls = {};
									for Idx = 1, #Lupvals do
										List = Lupvals[Idx];
										for Idz = 0, #List do
											Upv = List[Idz];
											NStk = Upv[1];
											DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 133) then
								if (Enum > 132) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 134) then
								local B;
								local T;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum <= 148) then
							if (Enum <= 141) then
								if (Enum <= 138) then
									if (Enum <= 136) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									elseif (Enum == 137) then
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
									end
								elseif (Enum <= 139) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								elseif (Enum > 140) then
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								else
									local DIP;
									local NStk;
									local Upv;
									local List;
									local Cls;
									local A;
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Cls = {};
									for Idx = 1, #Lupvals do
										List = Lupvals[Idx];
										for Idz = 0, #List do
											Upv = List[Idz];
											NStk = Upv[1];
											DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
								end
							elseif (Enum <= 144) then
								if (Enum <= 142) then
									local B = Stk[Inst[4]];
									if not B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								elseif (Enum == 143) then
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 146) then
								if (Enum == 145) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum == 147) then
								Stk[Inst[2]][Inst[3]] = Inst[4];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 155) then
							if (Enum <= 151) then
								if (Enum <= 149) then
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 150) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 153) then
								if (Enum == 152) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum == 154) then
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local A;
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
							end
						elseif (Enum <= 158) then
							if (Enum <= 156) then
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 157) then
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 160) then
							if (Enum > 159) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 161) then
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						else
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						end
					elseif (Enum <= 189) then
						if (Enum <= 175) then
							if (Enum <= 168) then
								if (Enum <= 165) then
									if (Enum <= 163) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum == 164) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										local A;
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 166) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 167) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]] = not Stk[Inst[3]];
								end
							elseif (Enum <= 171) then
								if (Enum <= 169) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
								elseif (Enum == 170) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] <= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 173) then
								if (Enum > 172) then
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 174) then
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 182) then
							if (Enum <= 178) then
								if (Enum <= 176) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 177) then
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A = Inst[2];
									local Results = {Stk[A]()};
									local Limit = Inst[4];
									local Edx = 0;
									for Idx = A, Limit do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 180) then
								if (Enum > 179) then
									local DIP;
									local NStk;
									local Upv;
									local List;
									local Cls;
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Cls = {};
									for Idx = 1, #Lupvals do
										List = Lupvals[Idx];
										for Idz = 0, #List do
											Upv = List[Idz];
											NStk = Upv[1];
											DIP = Upv[2];
											if ((NStk == Stk) and (DIP >= A)) then
												Cls[DIP] = NStk[DIP];
												Upv[1] = Cls;
											end
										end
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 181) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local T;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 185) then
							if (Enum <= 183) then
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 326) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							elseif (Enum > 184) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Upvalues[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 187) then
							if (Enum > 186) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum > 188) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 203) then
						if (Enum <= 196) then
							if (Enum <= 192) then
								if (Enum <= 190) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum > 191) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 194) then
								if (Enum > 193) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum > 195) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A;
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 199) then
							if (Enum <= 197) then
								local B;
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 198) then
								local Edx;
								local Results;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 201) then
							if (Enum == 200) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum == 202) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 210) then
						if (Enum <= 206) then
							if (Enum <= 204) then
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 205) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							else
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 208) then
							if (Enum == 207) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum > 209) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local B;
							local T;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 213) then
						if (Enum <= 211) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 212) then
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 215) then
						if (Enum > 214) then
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum == 216) then
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					else
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = #Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 326) then
					if (Enum <= 271) then
						if (Enum <= 244) then
							if (Enum <= 230) then
								if (Enum <= 223) then
									if (Enum <= 220) then
										if (Enum <= 218) then
											do
												return Stk[Inst[2]];
											end
										elseif (Enum == 219) then
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
										else
											local B;
											local A;
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 221) then
										local B;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = -Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = -Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Stk[Inst[4]];
										if not B then
											VIP = VIP + 1;
										else
											Stk[Inst[2]] = B;
											VIP = Inst[3];
										end
									elseif (Enum == 222) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
									end
								elseif (Enum <= 226) then
									if (Enum <= 224) then
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 225) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									end
								elseif (Enum <= 228) then
									if (Enum > 227) then
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum > 229) then
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local Edx;
									local Results;
									local A;
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 237) then
								if (Enum <= 233) then
									if (Enum <= 231) then
										Stk[Inst[2]] = Inst[3] ~= 0;
									elseif (Enum == 232) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 235) then
									if (Enum == 234) then
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									end
								elseif (Enum > 236) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 240) then
								if (Enum <= 238) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 239) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B;
									local T;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 242) then
								if (Enum == 241) then
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								elseif (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 243) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 257) then
							if (Enum <= 250) then
								if (Enum <= 247) then
									if (Enum <= 245) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum == 246) then
										Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
									else
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
									end
								elseif (Enum <= 248) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								elseif (Enum == 249) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 253) then
								if (Enum <= 251) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 252) then
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 255) then
								if (Enum > 254) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum > 256) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 264) then
							if (Enum <= 260) then
								if (Enum <= 258) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 259) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A]());
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 262) then
								if (Enum > 261) then
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								else
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum > 263) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local K;
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 267) then
							if (Enum <= 265) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							elseif (Enum > 266) then
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 269) then
							if (Enum > 268) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Top = (A + Varargsz) - 1;
								for Idx = A, Top do
									local VA = Vararg[Idx - A];
									Stk[Idx] = VA;
								end
							end
						elseif (Enum > 270) then
							VIP = Inst[3];
						else
							local B;
							local T;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 298) then
						if (Enum <= 284) then
							if (Enum <= 277) then
								if (Enum <= 274) then
									if (Enum <= 272) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum > 273) then
										local A;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
									end
								elseif (Enum <= 275) then
									Stk[Inst[2]] = {};
								elseif (Enum > 276) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = Inst[3];
									else
										VIP = VIP + 1;
									end
								end
							elseif (Enum <= 280) then
								if (Enum <= 278) then
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 279) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum <= 282) then
								if (Enum == 281) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								end
							elseif (Enum > 283) then
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 291) then
							if (Enum <= 287) then
								if (Enum <= 285) then
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								elseif (Enum > 286) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 289) then
								if (Enum == 288) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								else
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum == 290) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 294) then
							if (Enum <= 292) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum > 293) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 296) then
							if (Enum == 295) then
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum > 297) then
							Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
						else
							local A;
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 312) then
						if (Enum <= 305) then
							if (Enum <= 301) then
								if (Enum <= 299) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = #Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 300) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 303) then
								if (Enum > 302) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum == 304) then
								local K;
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 308) then
							if (Enum <= 306) then
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							elseif (Enum > 307) then
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							end
						elseif (Enum <= 310) then
							if (Enum == 309) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum == 311) then
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A]());
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 319) then
						if (Enum <= 315) then
							if (Enum <= 313) then
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Enum == 314) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Stk[Inst[3]] ^ Inst[4];
							end
						elseif (Enum <= 317) then
							if (Enum > 316) then
								local B;
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum == 318) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] ~= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 322) then
						if (Enum <= 320) then
							Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
						elseif (Enum == 321) then
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if not B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 324) then
						if (Enum > 323) then
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local Edx;
							local Results, Limit;
							local A;
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum == 325) then
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 381) then
					if (Enum <= 353) then
						if (Enum <= 339) then
							if (Enum <= 332) then
								if (Enum <= 329) then
									if (Enum <= 327) then
										local A;
										local K;
										local B;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									elseif (Enum > 328) then
										do
											return Stk[Inst[2]]();
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 330) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum > 331) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 335) then
								if (Enum <= 333) then
									local Results;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum == 334) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 337) then
								if (Enum > 336) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								else
									Stk[Inst[2]] = -Stk[Inst[3]];
								end
							elseif (Enum == 338) then
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 346) then
							if (Enum <= 342) then
								if (Enum <= 340) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 341) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local B;
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Stk[Inst[4]];
									if B then
										VIP = VIP + 1;
									else
										Stk[Inst[2]] = B;
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 344) then
								if (Enum == 343) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum > 345) then
								local B;
								local T;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 349) then
							if (Enum <= 347) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							elseif (Enum == 348) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 351) then
							if (Enum > 350) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum == 352) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]]();
						end
					elseif (Enum <= 367) then
						if (Enum <= 360) then
							if (Enum <= 356) then
								if (Enum <= 354) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 355) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local Edx;
									local Limit;
									local Results;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A]()};
									Limit = Inst[4];
									Edx = 0;
									for Idx = A, Limit do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Inst[2] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 358) then
								if (Enum == 357) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 359) then
								local B;
								local Edx;
								local Results, Limit;
								local A;
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 363) then
							if (Enum <= 361) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A], Stk[A + 1];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 362) then
								local B;
								local T;
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local B;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Stk[Inst[4]];
								if not B then
									VIP = VIP + 1;
								else
									Stk[Inst[2]] = B;
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 365) then
							if (Enum == 364) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum == 366) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 374) then
						if (Enum <= 370) then
							if (Enum <= 368) then
								local B;
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum == 369) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 372) then
							if (Enum > 371) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum == 373) then
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 377) then
						if (Enum <= 375) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A]());
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 376) then
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 379) then
						if (Enum == 378) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Upvalues[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B;
							local T;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum > 380) then
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Inst[3] do
							Insert(T, Stk[Idx]);
						end
					else
						local B;
						local T;
						local A;
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						T = Stk[A];
						B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					end
				elseif (Enum <= 408) then
					if (Enum <= 394) then
						if (Enum <= 387) then
							if (Enum <= 384) then
								if (Enum <= 382) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 383) then
									local B;
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 385) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 386) then
								local K;
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 390) then
							if (Enum <= 388) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 389) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 392) then
							if (Enum == 391) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum > 393) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 401) then
						if (Enum <= 397) then
							if (Enum <= 395) then
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum == 396) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 399) then
							if (Enum == 398) then
								local B;
								local A;
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum == 400) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Stk[Inst[4]]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 404) then
						if (Enum <= 402) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						elseif (Enum > 403) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local K;
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Stk[Inst[4]];
							if B then
								VIP = VIP + 1;
							else
								Stk[Inst[2]] = B;
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 406) then
						if (Enum == 405) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum > 407) then
						local A;
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local Results;
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A]());
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum <= 422) then
					if (Enum <= 415) then
						if (Enum <= 411) then
							if (Enum <= 409) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum > 410) then
								local K;
								local B;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 413) then
							if (Enum == 412) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum == 414) then
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 418) then
						if (Enum <= 416) then
							local B;
							local T;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						elseif (Enum > 417) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 420) then
						if (Enum == 419) then
							local Edx;
							local Results;
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum > 421) then
						local B;
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum <= 429) then
					if (Enum <= 425) then
						if (Enum <= 423) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						elseif (Enum > 424) then
							local Edx;
							local Results;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Stk[A + 1])};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 427) then
						if (Enum > 426) then
							local K;
							local B;
							local A;
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum == 428) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 432) then
					if (Enum <= 430) then
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum > 431) then
						local A;
						local K;
						local B;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
					end
				elseif (Enum <= 434) then
					if (Enum == 433) then
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local Results;
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A]());
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum == 435) then
					local A;
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Inst[3]));
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3] ~= 0;
					VIP = VIP + 1;
					Inst = Instr[VIP];
					VIP = Inst[3];
				else
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]]();
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]]();
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Upvalues[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					if Stk[Inst[2]] then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!E3022Q0003043Q0067616D6503083Q0049734C6F6164656403063Q004C6F6164656403043Q0057616974030A3Q004765745365727669636503073Q00506C6179657273030C3Q0054772Q656E5365727669636503103Q0055736572496E70757453657276696365030A3Q0052756E5365727669636503113Q005265706C69636174656453746F72616765030B3Q005669727475616C5573657203113Q00436F2Q6C656374696F6E53657276696365030B3Q00482Q747053657276696365030F3Q0054656C65706F727453657276696365030A3Q0053746172746572477569030A3Q004775695365727669636503083Q004C69676874696E67030B3Q004C6F63616C506C6179657203053Q007063612Q6C03093Q004F72696F6E2048756203043Q0076342E30034Q0003143Q004F72696F6E4875625F636F6E6669672E6A736F6E030A3Q0074772Q656E53702Q6564026Q00694003093Q0074772Q656E4D6F646503043Q004C65727003083Q006661726D44697374026Q00244003093Q00706F734D6574686F6403053Q0041626F766503063Q00776561706F6E03053Q004D656C2Q6503043Q0068616B692Q0103073Q00666163654D6F62010003063Q006E6F636C6970030A3Q006F72696F6E436C69636B030A3Q006F72696F6E4275727374026Q00F03F03093Q0061746B4D6574686F6403043Q004175746F03083Q0061746B44656C6179027B14AE47E17AA43F03093Q006D2Q6F6E52616E6765026Q004E40030B3Q006D2Q6F6E54617267657473026Q00284003043Q0066617374030A3Q00636865737453702Q6564030A3Q00667275697453702Q656403073Q00747053702Q656403053Q0073746F726503083Q00686F7044656C6179026Q00184003093Q00736561486569676874025Q0080414003083Q0073656153702Q656403093Q00736561536B692Q6C73030A3Q00626F2Q73486569676874026Q002C40030A3Q00626F2Q73536B692Q6C7303063Q0061696D43616D03043Q006661726D03053Q00636865737403053Q00626F6E657303043Q0063616B6503093Q0063616B65517565737403093Q0069676E6F72654B617403053Q00656C69746503093Q006B692Q6C496E64726103083Q0073756D496E64726103043Q0070616473030A3Q006B692Q6C52656170657203093Q0073756D52656170657203093Q006B692Q6C426561726403083Q0073756D426561726403083Q00686F70426561726403043Q00734C657603073Q00734C657653656703063Q0073426561737403063Q0073536861726B03083Q0073506972616E686103053Q00734669736803063Q007347686F737403053Q0066727569742Q033Q00686F7003073Q0062617274696C6F03073Q00636974697A656E03063Q0072616365563203063Q0072616365563303043Q007261696403083Q00726169645479706503053Q00466C616D6503073Q006275794368697003083Q00626164467275697403063Q006177616B656E03053Q00616374563303053Q0061637456342Q033Q0061666B03063Q0061666B4D696E026Q00144003083Q00667073422Q6F737403063Q006670734D6178030A3Q00657370506C617965727303093Q0065737046727569747303093Q00657370436865737473030A3Q0065737042652Q7269657303093Q0065737049736C616E6403073Q0065737044697374030A3Q006573704F75746C696E6503053Q007370644F6E03083Q0073702Q656456616C026Q0049402Q033Q0063666D03043Q00696E666A03093Q0077616C6B576174657203063Q0069736C616E64030A3Q0073616265725374616765030B3Q007361626572506C6174657303093Q0073616265724275726E03053Q00736162657203093Q0073656132517565737403093Q0073656133517565737403093Q006175746F537461747303073Q007374617450657203083Q00737461744C656674030A3Q004175746F6D617469636F03093Q00737461744D656C2Q65030B3Q0073746174446566656E736503093Q007374617453776F726403073Q007374617447756E03093Q0073746174467275697403083Q00496E7374616E63652Q033Q006E657703093Q005363722Q656E47756903043Q004E616D6503053Q004F52494F4E030C3Q0052657365744F6E537061776E030E3Q0049676E6F7265477569496E736574030E3Q005A496E6465784265686176696F7203043Q00456E756D03073Q005369626C696E6703063Q00506172656E74030C3Q0057616974466F724368696C6403093Q00506C6179657247756903023Q00626703063Q00436F6C6F723303073Q0066726F6D524742026Q002640026Q00314003043Q0073696465026Q002E40026Q00374003043Q0063617264026Q00414003043Q006C696E65026Q004440026Q004D402Q033Q00747874025Q00806D40025Q00C06E402Q033Q006D7574025Q00805F40026Q006040026Q0063402Q033Q006F2Q66026Q004A40025Q008051402Q033Q00612Q63025Q00606140026Q00574003043Q00612Q6332025Q00C05840025Q00805940025Q00206E4003093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503073Q00566563746F7232026Q009440025Q0080864003043Q006D6174682Q033Q006D696E025Q00A0844003013Q0058026Q003440025Q00807B4003013Q005903053Q004672616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q6673657403083Q00506F736974696F6E026Q00E03F027Q004003103Q004261636B67726F756E64436F6C6F7233030F3Q00426F7264657253697A65506978656C028Q0003083Q0055495374726F6B6503093Q00546869636B6E652Q73026Q00F83F03053Q00436F6C6F72030C3Q005472616E73706172656E637902CD5QCCDC3F026Q004B4003163Q004261636B67726F756E645472616E73706172656E637903093Q00546578744C6162656C025Q00406F40026Q003840026Q003040026Q00204003043Q0054657874032B3Q002Q203C666F6E7420636F6C6F723D22726762283133392C39322C32343629223E4E4558543C2F666F6E743E03083Q005269636854657874030A3Q0054657874436F6C6F723303043Q00466F6E74030A3Q00476F7468616D426F6C6403083Q005465787453697A65030E3Q005465787458416C69676E6D656E7403043Q004C656674025Q00C07240026Q003F40030E3Q00426C6F7820467275697420C2B72003063Q00476F7468616D03073Q0054657874426F78025Q00C06240026Q003C40025Q00A074C0026Q002A40030F3Q00506C616365686F6C6465725465787403093Q005365617263683Q2E03113Q00506C616365686F6C646572436F6C6F723303103Q00436C656172546578744F6E466F63757303093Q00554950612Q64696E67030B3Q0050612Q64696E674C65667403043Q005544696D03013Q0078026Q0043C003013Q002D025Q008051C003073Q00436F6E6669672E025Q004062C003113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374026Q0034C0030A3Q00496E707574426567616E030C3Q00496E7075744368616E676564030A3Q00496E707574456E646564030A3Q005465787442752Q746F6E026Q003BC0030F3Q004175746F42752Q746F6E436F6C6F7203063Q005A496E64657803103Q00436C69707344657363656E64616E7473026Q003B40030A3Q0055494772616469656E74030D3Q00436F6C6F7253657175656E6365026Q003A40026Q003E40025Q00805040026Q001C40026Q00324003083Q00526F746174696F6E025Q0080494003063Q006D65692Q736102EC51B81E85EBC13F03053Q00626574656C021F85EB51B81ED53F0248E17A14AE47D13F03053Q0062652Q6C6102C3F5285C8FC2E53F03073Q006D696E74616B610285EB51B81E85E33F02A4703D0AD7A3E03F03073Q00616C6E696C616D0252B81E85EB51E03F0248E17A14AE47E13F03073Q00616C6E6974616B023D0AD7A3703DDA3F02EC51B81E85EBE13F03053Q00736169706802AE47E17A14AED73F029A5Q99E93F03053Q00726967656C02B81E85EB51B8E63F0248E17A14AE47E93F03063Q00697061697273025Q00E06F40025Q00C06740025Q00406540025Q00406A40025Q00206C40026Q000840025Q00806B4003043Q007461736B03053Q00737061776E030E3Q005363726F2Q6C696E674672616D65025Q008050C0026Q004F4003123Q005363726F2Q6C426172546869636B6E652Q73030A3Q0043616E76617353697A6503133Q004175746F6D6174696343616E76617353697A65030D3Q004175746F6D6174696353697A65030C3Q0055494C6973744C61796F757403073Q0050612Q64696E67025Q008063C0026Q0051C0025Q0040624003183Q0047657450726F70657274794368616E6765645369676E616C03083Q0053652Q74696E677303043Q004D61696E030A3Q004D756C7469204661726D03063Q0051756573747303043Q005261636503053Q00526169647303093Q00536561204576656E7403063Q0046727569747303083Q004C6F636174696F6E2Q033Q0045535003063Q00506C6179657203083Q004469766572736F7303023Q006F7303053Q00636C6F636B022Q00A053AD84E441022Q00701B7B8CF041022Q0030F152C0FB4103073Q00506C616365496403073Q005374652Q70656403043Q004D2Q6F6E03023Q0043462Q033Q0043463203063Q0052656D6F746503053Q00436C69636B030F3Q00436F6D6261744672616D65776F726B03113Q00436F6D6261744672616D65776F726B203203013Q006D03023Q00687003063Q006C617374487003073Q006C617374446D6703043Q006E65617203053Q00726561647903093Q0048656172746265617403123Q0054656C65706F7274496E69744661696C656403043Q006C69737403053Q007761734F6E03083Q00636C65616E75707303053Q007461626C6503063Q00696E73657274030E3Q007265626F726E736B656C65746F6E030C3Q006C6976696E677A6F6D626965030B3Q0064656D6F6E6963736F756C030D3Q00706F73652Q7365646D752Q6D79030E3Q00706F2Q73652Q7365646D752Q6D79030D3Q00632Q6F6B69656372616674657203093Q0063616B656775617264030B3Q0062616B696E677374612Q6603093Q006865616462616B6572025Q00804B4003083Q00726970696E64726103093Q0052697020496E647261030A3Q00736F756C726561706572030B3Q00536F756C2052656170657203093Q006461726B6265617264030B3Q004261726261204E656772612Q033Q0073656103043Q006974656D030B3Q00676F64736368616C69636503083Q006974656D4E616D65030D3Q00476F642773204368616C6963652Q033Q006C6F63030E3Q00636173746C656F6E74686573656103063Q00636173746C6503053Q00706C61636503133Q006F20436173746C65206F6E207468652053656103083Q0070612Q7465726E7303083Q00706564657374616C03073Q006368616C69636503063Q0073752Q6D6F6E03053Q00616C74617203053Q00696E64726103043Q0068696E74032C3Q00636F6E66697261207365206F73203320626F746F6573206465204175726120657374616F20617469766F732E030D3Q0068612Q6C6F77652Q73656E6365030E3Q0048612Q6C6F7720452Q73656E6365030D3Q006861756E746564636173746C6503073Q006861756E74656403103Q006F204861756E74656420436173746C6503063Q0068612Q6C6F77031F3Q006F20616C746172206669636120706572746F20646F206D6175736F6C65752E030E3Q00666973746F666461726B6E652Q7303103Q0046697374206F66204461726B6E652Q7303093Q006461726B6172656E6103043Q006461726B030C3Q0061204461726B204172656E6103043Q006669737403213Q006F20706564657374616C2066696361206E6F206D65696F206461206172656E612E025Q004050402Q033Q006B657903053Q006C6162656C030E3Q004B692Q6C204C657669617468616E03053Q006E616D657303093Q006C657669617468616E031A3Q004B692Q6C204C657669617468616E20287365676D656E746F732903083Q007365676D656E7473030E3Q004B692Q6C2053656120426561737403083Q00736561626561737403103Q004B692Q6C2054652Q726F72736861726B030B3Q0074652Q726F72736861726B030C3Q004B692Q6C20506972616E686103073Q00706972616E6861030E3Q004B692Q6C2046697368204372657703083Q00666973686372657703233Q004B692Q6C204861756E7465642053686970777265636B202847686F7374205368697029030B3Q006861756E74656463726577030A3Q0067686F7374736861726B030C3Q00736869706465636B68616E64030C3Q0073686970656E67696E2Q6572030B3Q007368697073746577617264030B3Q00736869706F2Q6669636572030D3Q006375727365646361707461696E026Q0039402Q033Q00696E7603043Q006261736503073Q00736B692Q70656403053Q00747269657303063Q00696E69746564030B3Q006C6173745265667265736803093Q006E6F6E6553696E636503063Q004368657374312Q033Q0042617503063Q00436865737432030C3Q0042617520646520507261746103063Q00436865737433030B3Q00426175206465204F75726F03043Q00646F6E6503073Q007669736974656403043Q007374657003073Q006C61737447657403083Q00612Q6365707465642Q033Q0049636503053Q005175616B6503053Q004C6967687403043Q004461726B03063Q0053706964657203063Q0052756D626C6503053Q004D61676D6103063Q0042752Q64686103043Q0053616E6403073Q0050686F656E697803053Q00446F75676803063Q00726F636B657403043Q007370696E03053Q00626C61646503063Q00737072696E67026Q00104003043Q00626F6D6203053Q00736D6F6B6503053Q007370696B6503053Q00666C616D6503063Q0066616C636F6E026Q0022402Q033Q0069636503043Q0073616E6403073Q006469616D6F6E6403053Q006C6967687403063Q0072752Q62657203073Q0062612Q7269657203053Q0067686F737403053Q006D61676D61025Q0080464003053Q0049646C656403073Q0053656374696F6E03093Q004175746F204661726D03073Q0046656174757265030F3Q004175746F204661726D204C6576656C03053Q006772696E64030A3Q004175746F20436865737403163Q00426F6E657320284861756E74656420436173746C6529030A3Q004175746F20426F6E657303143Q004B6174616B757269202843616B65204C616E642903123Q004175746F204661726D204B6174616B75726903063Q00546F2Q676C6503103Q0049676E6F726172204B6174616B75726903243Q00536F206661726D61206F73206D6F62732C2073656D20617461636172206F20626F2Q732E030E3Q004B6174616B75726920517565737403283Q004661726D2053652Q74696E677320286D61697320616A757374657320656D2053652Q74696E67732903063Q00536C69646572030E3Q0054772Q656E696E672053702Q6564032C3Q0056656C6F63696461646520646F2074772Q656E20656D2073747564732F7320286D6178696D6F20322Q30292E03093Q004175746F2048616B6903213Q004C696761206F204275736F2048616B69206175746F6D61746963616D656E74652E030A3Q004661737420436C69636B033E3Q00436C697175652072617069646F206E6F73206D6F6273202874726F6361206465206D65746F646F20736F7A696E686F207365206E616F206261746572292E030B3Q004F72696F6E20436C69636B03633Q00537570657220636C69636B3A20756D20676F6C706520706F72206672616D65206F75206D6169732C206D6169732072617069646F20717565206F204661737420436C69636B202876616C6F72657320616C746F7320706F64656D206B69636B6172292E03043Q004E6F746503753Q004D756C7469204661726D3A20636F6D62696E6520616C766F73206520617469766964616465732E2046756E636F6573206465207072696F726964616465202866727574612C20626F2Q7365732920696E74652Q726F6D70656D206F206661726D206520656C6520766F6C746120736F7A696E686F2E030C3Q00456C6974652048756E74657203113Q004175746F20456C6974652048756E746572030E3Q00426F2Q732052697020496E647261030E3Q004B692Q6C2052697020496E64726103103Q0053752Q6D6F6E2052697020496E64726103133Q004175746F20546F756368205061642048616B6903103Q00426F2Q7320536F756C2052656170657203103Q004B692Q6C20536F756C2052656170657203123Q0053752Q6D6F6E20536F756C2052656170657203093Q004461726B6265617264030E3Q004B692Q6C204461726B626561726403103Q0053752Q6D6F6E204461726B626561726403143Q00486F7020536572766572204461726B626561726403113Q00416C74757261206E6F7320626F2Q73657303123Q0044697374616E63696120646F20626F2Q732E03113Q00536B692Q6C73206E6F7320626F2Q736573030C3Q00557361205A2058204320562E03053Q005365612031030B3Q00517565737420536162657203063Q0042752Q746F6E031A3Q00526573657461722070726F6772652Q736F20646F20536162657203443Q004170616761206F2070726F6772652Q736F2073616C766F206461205175657374205361626572207061726120726566617A657220746F646173206173206574617061732E03073Q005265736574617203103Q005175657374205365636F6E642053656103053Q00536561203203123Q004175746F2042617274696C6F205175657374030F3Q0051756573742054686972642053656103053Q00536561203303123Q004175746F20436974697A656E20517565737403FD3Q005175657374205361626572202F205365636F6E6420536561202F205468697264205365613A206D656C686F72206573666F72636F20286174616361206F7320626F2Q736573206520757361206F7320636F6D616E646F7320646F206A6F676F293B207061727465732064652070752Q7A6C652073616F206D616E756169732E2042617274696C6F3A205377616E20506972617465732065204A6572656D792073616F206175746F6D617469636F733B206120706172746520646F20436F6C697365752065206D616E75616C2E20436974697A656E3A207065676120612071756573742065206D617461206F204361707461696E20456C657068616E742E03163Q00446574656374616E646F2073756120726163613Q2E03083Q0045766F6C7563616F03183Q004175746F20526163652056322028416C6368656D69737429030C3Q004175746F2052616365205633038D3Q0056323A20616365697461206120717565737420646F20416C6368656D6973742C206A756E7461206173203320666C6F726573206520656E74726567612E2056333A2076616920617465206F204E50432065207065646520612071756573743B206F20747269616C206461207261636120766F636520636F6E636C75692073656775696E646F206F206A6F676F2E03043Q004368697003083Q0044726F70646F776E030B3Q0053656C6563742052616964031A3Q005175616C207261696420766F636520717565722066617A65722E030D3Q004175746F20427579204368697003193Q005061676172206368697020636F6D206672757461207275696D03423Q005573612061206672757461206D61697320626172617461206461206D6F6368696C6120286E756E636120617320626F61732920656D2076657A2064652062656C692E03043Q0052616964030E3Q004175746F204661726D205261696403113Q004175746F204177616B656E204672756974036B3Q004175746F205261696420696E696369612061207261696420736F7A696E686F207175616E646F20766F63652074656D206F206368697020652C2064656E74726F2064656C612C20766F6120617465206F7320696E696D69676F7320636F6D206661737420612Q7461636B2E03153Q005472616E73666F726D6163616F2064612072616361030E3Q004175746F2041746976617220563303303Q00417065727461205920736F7A696E686F207175616E646F206120656E6572676961206461207261636120656E6368652E030E3Q004175746F2041746976617220563403103Q004D65736D6F207061726120612056342E033D3Q0041746976612061207472616E73666F726D6163616F2064612072616361206175746F6D61746963616D656E746520647572616E7465206F206661726D2E03643Q004C6967756520756D206F75206D616973206576656E746F732065206669717565206E6F206D61722E20456C6520657370657261206F206D6F6E7374726F2061706172656365722C20766F612061746520656C6520652061746163612064652063696D612E03113Q005374617475733A206465736C696761646F03073Q004576656E746F7303163Q004174616361207175616E646F2061706172656365722E03073Q00416A757374657303133Q00416C7475726120736F627265206F20616C766F03173Q005374756473206163696D6120646F206D6F6E7374726F2E026Q00594003153Q0056656C6F63696461646520617465206F20616C766F03153Q0073747564732F7320286D6178696D6F20322Q30292E03123Q00536B692Q6C73206E6F73206576656E746F7303263Q00557361205A20582043205620286E6563652Q736172696F206E6F204C657669617468616E292E03153Q005472617661722063616D657261206E6F20616C766F03093Q004F7063696F6E616C2E030F3Q004175746F2046696E64204672756974030A3Q0053657276657220486F70034A3Q0054726F6361206465207365727669646F72207175616E646F206E616F2074656D2066727574612028736F207365206E656E68756D206661726D2065737469766572206C696761646F292E030F3Q0041726D617A656E617220667275746103263Q004775617264612061206672757461206E6F20696E76656E746172696F20616F2070656761722E03183Q004573706572617220616E74657320646F20686F702028732903203Q0054656D706F2073656D20667275746120616E7465732064652074726F6361722E03163Q0056656C6F636964616465206174652061206672757461032F3Q004D696E6861732066727574617320646574656374616461733A202861696E6461206E616F2064657465637461646F2903123Q0054726F636172206465207365727669646F72031E3Q005661692070617261206F7574726F207365727669646F722061676F72612E2Q033Q00486F7003173Q00417475616C697A6172206D696E68617320667275746173031C3Q004C652061206D6F6368696C612065206F20696E76656E746172696F2E03093Q00417475616C697A617203293Q004573636F6C686120756D6120696C68612065206C696775652054656C65706F72742049736C616E642E030F3Q0049736C616E642054656C65706F7274030A3Q004553502049736C616E6403263Q004D6F73747261206F206E6F6D65206520612064697374616E6369612064617320696C6861732E030D3Q0053656C6563742049736C616E6403213Q0053656C6563696F6E61206120696C686120706172612074656C65706F727461722E030F3Q0054656C65706F72742049736C616E6403493Q0054656C65706F72746120617465206120696C68612073656C6563696F6E61646120285375626D65726765642049736C616E6420656E7472612070656C6F207375626D6172696E6F292E03043Q007470476F03173Q0056656C6F63696461646520646F2074656C65706F727465030F3Q00417475616C697A617220696C686173031F3Q00526563612Q726567612061206C6973746120646F206D617220617475616C2E03123Q005669616A617220656E747265206D61726573031A3Q005669616A612070617261206F207072696D6569726F206D61722E03023Q00497203193Q005669616A612070617261206F20736567756E646F206D61722E031A3Q005669616A612070617261206F20746572636569726F206D61722E030B3Q0045535020506C617965727303133Q004D61726361206F73206A6F6761646F7265732E030A3Q004553502046727569747303153Q004D6172636120667275746173206E6F206368616F2E030A3Q004553502043686573747303123Q004D61726361206261757320617469766F732E030B3Q004553502042652Q72696573031D3Q004D61726361206F73206172627573746F732064652062652Q726965732E03113Q004D6F73747261722064697374616E63696103123Q004D6574726F7320617465206F20616C766F2E03093Q00436F6E746F726E6F7303283Q00436F6E746F726E6F20636F6C6F7269646F20656D206A6F6761646F7265732065206672757461732E03053Q0053702Q656403203Q0041756D656E746120612076656C6F63696461646520646520636F2Q726964612E030A3Q0056656C6F636964616465030F3Q0056616C6F7220646F2073702Q65642E030B3Q004D6F646F20434672616D6503233Q00557365207365206F206A6F676F207265736574617220612076656C6F6369646164652E030D3Q0050756C6F20696E66696E69746F03183Q0050756C61207661726961732076657A6573206E6F2061722E030D3Q0057616C6B206F6E20576174657203123Q00416E646120736F627265206120616775612E030B3Q004A756D705265717565737403083Q00416E74692041464B033C3Q00436C696361206E612074656C612064652074656D706F7320656D2074656D706F732070617261206F206A6F676F206E616F207465206B69636B61722E03133Q00496E74657276616C6F20286D696E75746F7329031E3Q00412063616461207175616E746F73206D696E75746F7320636C696361722E033F3Q00416C656D20646F20636C697175652C206F20416E74692041464B20646F20526F626C6F78202849646C65642920666963612073656D70726520617469766F2E030B3Q004175746F20537461747573030B3Q004D756C746953656C656374030D3Q0053656C6563742053746174757303343Q004573636F6C6861206F6E646520636F6C6F636172206F7320706F6E746F732028706F6465206D617263617220766172696F73292E030C3Q00536F636F20284D656C2Q652903103Q004465666573612028446566656E73652903053Q0053776F72642Q033Q0047756E03123Q0046727574612028426C6F782046727569742903113Q00506F6E746F7320706F722073746174757303433Q005175616E746F7320706F6E746F732076616F20656D206361646120737461747573206573636F6C6869646F2061206361646120726F64616461202865782E3A2031292E030F3Q00536F62726120646520706F6E746F73035A3Q0050617261206F6E64652076616F206F7320706F6E746F732071756520736F62726172656D2E204175746F6D617469636F203D206F20737461747573206573636F6C6869646F207175652065737461206D61697320626169786F2E03073Q00446566656E7365030B3Q0044656D6F6E20467275697403163Q004175746F205374617475733A206465736C696761646F03573Q00446973747269627569206F7320706F6E746F7320646973706F6E69766569733A204E20656D206361646120737461747573206D61726361646F2065206120736F627261206E6F2073746174757320646120736F6272612E030A3Q00446573656D70656E686F03093Q0046505320422Q6F7374033D3Q005469726120736F6D627261732C2065666569746F73206520706172746963756C6173207061726120646569786172206F20526F626C6F78206C69736F2E03103Q0046505320422Q6F7374206D6178696D6F03413Q0054616D62656D2073696D706C6966696361206D6174657269616973206520746578747572617320286E616F2064657366617A2073656D20722Q656E74726172292E03173Q0041706C696361722046505320422Q6F73742061676F726103183Q00457865637574612061206C696D70657A612061676F72612E03073Q0041706C69636172030A3Q00537562324665723Q39030B3Q00456E79755F69735F50726F03083Q004D6167696362757303043Q004A43574B030B3Q0053746172636F646568656F03063Q00426C752Q787903063Q0066752Q64313003093Q0066752Q6431305F763203133Q005355423247414D452Q524F424F545F4558503103113Q00537562324E2Q6F624D6173746572313233030F3Q0053756232556E636C654B697A617275030C3Q005375623244616967726F636B03063Q004178696F7265030C3Q0054616E74616947616D696E67030D3Q0053747261774861744D61696E6503123Q00537562324F2Q66696369616C4E2Q6F626965030B3Q005468654772656174416365030A3Q004B492Q545F524553455403073Q004269676E65777303053Q00555044313603053Q00555044313503053Q00555044313403053Q00555044313303053Q00555044313203053Q005550442Q3103053Q005550443130030A3Q004E4F4D4F52454841434B030D3Q0047414D452Q524F424F545F5954030C3Q00434F44455F53455256494345030B3Q0041444D494E5F54524F2Q4C030A3Q006B692Q7467616D696E6703083Q004368616E646C657203063Q004558505F354203073Q003342564953495403083Q003242492Q4C494F4E03083Q00544849524453454103093Q00464F5552544853454103083Q0052455345545F3542030C3Q005345435245545F41444D494E030B3Q005374612Q6642612Q746C6503153Q005355423247414D452Q524F424F545F524553455431030C3Q005265642Q656D20436F64657303303Q005265736761746120746F646F73206F7320636F6469676F7320646973706F6E697665697320646520756D612076657A2E03083Q005265736761746172032B3Q00416A757374657320646520436C69636B20286C6967612F6465736C696761206E6120616261204D61696E29031D3Q004F72696F6E20436C69636B3A20676F6C70657320706F72206672616D65035F3Q0031203D20756D20676F6C706520706F72206672616D6520286A61206D6169732072617069646F20717565206F204661737420436C69636B292E204D61696F72203D206D6169732072617069646F2065206D61697320612Q7269736361646F2E03063Q004D65746F646F03303Q004175746F2074726F6361206465206D65746F646F20736F7A696E686F207365206E616F206361757361722064616E6F2E2Q033Q00412Q6C03173Q00496E74657276616C6F20646F206174617175652028732903143Q004D656E6F72203D206D6169732072617069646F2E027B14AE47E17A943F029A5Q99C93F03173Q00416C63616E636520646F204D2Q6F6E202873747564732903253Q004D6F62732064656E74726F2064652Q7365207261696F206C6576616D206F20676F6C70652E026Q005E4003163Q004D61782E206465206D6F627320706F7220676F6C706503263Q005175616E746F73206D6F6273206F204D2Q6F6E2061636572746120646520756D612076657A2E03043Q004661726D030D3Q0053656C65637420576561706F6E03153Q0041726D61207573616461206E6F73206661726D732E030A3Q00426C6F78204672756974030C3Q0054772Q656E204F7074696F6E032A3Q004D65746F646F206465206D6F76696D656E746F20284C6572702065206F206D616973207375617665292E03053Q0054772Q656E03183Q0056656C6F63696461646520646F204175746F204368657374030D3Q004661726D2044697374616E6365031B3Q00416C747572612F64697374616E63696120617465206F206D6F622E030A3Q00506F73204D6574686F64031D3Q004F6E646520666963617220656D2072656C6163616F20616F206D6F622E03063Q00426568696E6403053Q0042656C6F7703103Q004F6C6861722070617261206F206D6F6203153Q00506F64652074726176617220612063616D6572612E03053Q00476572616C031E3Q004E6F636C6970206E61732066756E636F6573206175746F6D61746963617303213Q004174726176652Q7361207061726564657320647572616E7465206F206661726D2E03043Q004D656E7503233Q004573636F6E6465206F206D656E752028526967687453686966742074616D62656D292E03083Q004573636F6E64657203063Q0046656368617203123Q004665636861206F204F72696F6E204875622E03073Q00436F6E6578616F03123Q00436F6E65637461646F2068612030206D696E033A3Q004F20636F6E7461646F72207265696E69636961207175616E646F206F2073637269707420652065786563757461646F206E6F76616D656E74652E03013Q003F03053Q007072696E7403013Q005B030B3Q005D2063612Q72656761646F00A50D2Q001288012Q00013Q00208D5Q00022Q009C012Q00020002000657012Q00090001000100040F012Q00090001001288012Q00013Q0020E35Q000300208D5Q00042Q00333Q00020001001288012Q00013Q00208D5Q0005001216000200064Q00FC3Q000200020012052Q0100013Q00202Q00010001000500122Q000300076Q00010003000200122Q000200013Q00202Q00020002000500122Q000400086Q00020004000200122Q000300013Q00202Q000300030005001216000500094Q00FC000300050002001205010400013Q00202Q00040004000500122Q0006000A6Q00040006000200122Q000500013Q00202Q00050005000500122Q0007000B6Q00050007000200122Q000600013Q00202Q0006000600050012160008000C4Q00FC000600080002001205010700013Q00202Q00070007000500122Q0009000D6Q00070009000200122Q000800013Q00202Q00080008000500122Q000A000E6Q0008000A000200122Q000900013Q00202Q000900090005001216000B000F4Q00FC0009000B0002001288010A00013Q00208D000A000A0005001216000C00104Q00FC000A000C0002001288010B00013Q00208D000B000B0005001216000D00114Q00FC000B000D00020020E3000C3Q00122Q0062000D000D3Q001288010E00133Q0006B7000F3Q000100012Q0046012Q000D4Q0033000E00020001001216000E00143Q001216000F00153Q001216001000163Q001216001100174Q001301123Q002400305400120018001900302Q0012001A001B00302Q0012001C001D00302Q0012001E001F00302Q00120020002100302Q00120022002300302Q00120024002500302Q00120026002300302Q00120027002500302Q0012002800290030540012002A002B00302Q0012002C002D00302Q0012002E002F00302Q00120030003100302Q00120032002300302Q00120033001900302Q00120034001900302Q00120035001900302Q00120036002300302Q00120037003800305400120039003A00302Q0012003B001900302Q0012003C002300302Q0012003D003E00302Q0012003F002300302Q00120040002500302Q00120041002500302Q00120042002500302Q00120043002500302Q00120044002500305400120045002500302Q00120046002500302Q00120047002500302Q00120048002500302Q00120049002500302Q0012004A002500302Q0012004B002500302Q0012004C002500302Q0012004D002500302Q0012004E00250030540012004F002500302Q00120050002500302Q00120051002500302Q00120052002500302Q00120053002500302Q00120054002500302Q00120055002500302Q00120056002500302Q00120057002500302Q00120058002500305400120059002500302Q0012005A002500302Q0012005B002500302Q0012005C002500302Q0012005D002500302Q0012005E005F00302Q00120060002500302Q00120061002300302Q00120062002500302Q00120063002500305400120064002500302Q00120065002300302Q00120066006700302Q00120068002500302Q00120069002500302Q0012006A002500302Q0012006B002500302Q0012006C002500302Q0012006D002500302Q0012006E00250030540012006F002300302Q00120070002300302Q00120071002500302Q00120072007300302Q00120074002500302Q00120075002500302Q00120076002500302Q00120077001600302Q00120078002900302Q0012007900250030540012007A002500302Q0012007B002500302Q0012007C002500302Q0012007D002500302Q0012007E002500302Q0012007F002900302Q00120080008100302Q00120082002500302Q00120083002500302Q001200840025003093001200850025003093001200860025001288011300133Q0006B700140001000100032Q0046012Q00114Q0046012Q00074Q0046012Q00124Q00330013000200010030930012004100252Q00E700135Q0006B700140002000100042Q0046012Q00134Q0046012Q00114Q0046012Q00074Q0046012Q00123Q001288011500133Q000285001600034Q0033001500020001000285001500043Q001288011600133Q0006B700170005000100012Q0046012Q00154Q0033001600020001001288011600133Q0006B700170006000100022Q0046012Q00154Q0046012Q000C4Q0033001600020001001288011600133Q0006B700170007000100012Q0046012Q00154Q0033001600020001001288011600873Q0020E3001600160088001216001700894Q009C0116000200020030930016008A008B0030930016008C00250030930016008D00230012880117008F3Q0020E300170017008E0020E300170017009000105D0116008E0017001288011700133Q0006B700180008000100012Q0046012Q00164Q009C01170002000200069A011700D200013Q00040F012Q00D200010020E3001800160091000657011800D60001000100040F012Q00D6000100208D0018000C0092001216001A00934Q00FC0018001A000200105D0116009100182Q001301183Q0009001254011900953Q00202Q00190019009600122Q001A00973Q00122Q001B00973Q00122Q001C00986Q0019001C000200102Q00180094001900122Q001900953Q00202Q00190019009600122Q001A009A3Q001216001B009A3Q001216001C009B4Q00AF0019001C000200102Q00180099001900122Q001900953Q00202Q00190019009600122Q001A009B3Q00122Q001B009B3Q00122Q001C009D6Q0019001C000200102Q0018009C001900122Q001900953Q0020E3001900190096001216001A009F3Q001216001B009F3Q001216001C00A04Q00AF0019001C000200102Q0018009E001900122Q001900953Q00202Q00190019009600122Q001A00A23Q00122Q001B00A23Q00122Q001C00A36Q0019001C000200102Q001800A1001900122Q001900953Q0020E3001900190096001216001A00A53Q001216001B00A63Q001216001C00A74Q00AF0019001C000200102Q001800A4001900122Q001900953Q00202Q00190019009600122Q001A00733Q00122Q001B00A93Q00122Q001C00AA6Q0019001C000200102Q001800A8001900122Q001900953Q0020E3001900190096001216001A00AC3Q001216001B00AD3Q001216001C00A34Q00FC0019001C000200105D011800AB0019001288011900953Q0020E3001900190096001216001A00AF3Q001216001B00B03Q001216001C00B14Q00FC0019001C000200105D011800AE0019000285001900093Q0006B7001A000A000100012Q0046012Q00193Q000285001B000B3Q000285001C000C4Q00E7001D6Q00E7001E6Q00E7001F6Q001301205Q0006B70021000D000100012Q0046012Q00203Q0006B70022000E000100042Q0046012Q001D4Q0046012Q00204Q0046012Q00034Q0046012Q00163Q001288012300133Q0006B70024000F000100012Q0046012Q00224Q0033002300020001001288012300B23Q0020E30023002300B300069A012300312Q013Q00040F012Q00312Q010020E30024002300B4000657012400362Q01000100040F012Q00362Q01001288012400B53Q0020E3002400240088001216002500B63Q001216002600B74Q00FC002400260002001288012500B83Q0020E30025002500B9001216002600BA3Q0020E30027002400BB0020780027002700BC2Q00FC002500270002001288012600B83Q0020E30026002600B9001216002700BD3Q0020E30028002400BE0020780028002800BC2Q00FC0026002800022Q0046012700193Q001216002800BF4Q001301293Q0004001288012A00C13Q0020E3002A002A00C22Q0046012B00254Q0046012C00264Q00FC002A002C000200105D012900C0002A001288012A00C13Q0020E3002A002A0088001216002B00C44Q0050012C00253Q0020EA002C002C00C5001216002D00C44Q0050012E00263Q0020EA002E002E00C52Q00FC002A002E000200105D012900C3002A0020E3002A0018009400105D012900C6002A003093002900C700C82Q0046012A00164Q00FC0027002A00022Q00460128001A4Q0046012900273Q001216002A003E4Q00EE0028002A00012Q0046012800193Q001216002900C94Q0013012A3Q0003003093002A00CA00CB0020E3002B001800AB00105D012A00CC002B003093002A00CD00CE2Q0046012B00274Q00EE0028002B00012Q0046012800193Q00121E002900BF6Q002A3Q000200122Q002B00C13Q00202Q002B002B008800122Q002C00293Q00122Q002D00C83Q00122Q002E00C83Q00122Q002F00CF6Q002B002F000200102Q002A00C0002B003093002A00D000292Q0046012B00274Q00FC0028002B00022Q0046012900193Q001216002A00D14Q0013012B3Q0009001288012C00C13Q0020E3002C002C00C2001216002D00D23Q001216002E00D34Q00FC002C002E000200105D012B00C0002C001288012C00C13Q0020E3002C002C00C2001216002D00D43Q001216002E00D54Q00FC002C002E000200105D012B00C3002C003093002B00D000292Q0046012C000E3Q001216002D00D74Q0087002C002C002D001077002B00D6002C00302Q002B00D8002300202Q002C001800A100102Q002B00D9002C00122Q002C008F3Q00202Q002C002C00DA00202Q002C002C00DB00102Q002B00DA002C00302Q002B00DC00D400122Q002C008F3Q00202Q002C002C00DD00202Q002C002C00DE00102Q002B00DD002C4Q002C00286Q0029002C00024Q002A00193Q00122Q002B00D16Q002C3Q000800122Q002D00C13Q00202Q002D002D00C200122Q002E00DF3Q00122Q002F00D46Q002D002F000200102Q002C00C0002D00122Q002D00C13Q00202Q002D002D00C200122Q002E00D43Q00122Q002F00E06Q002D002F000200102Q002C00C3002D00302Q002C00D0002900122Q002D00E16Q002E000F6Q002D002D002E00102Q002C00D6002D00202Q002D001800A400102Q002C00D9002D00122Q002D008F3Q00202Q002D002D00DA00202Q002D002D00E200102Q002C00DA002D00302Q002C00DC009700122Q002D008F3Q00202Q002D002D00DD00202Q002D002D00DE00102Q002C00DD002D4Q002D00286Q002A002D00024Q002B00193Q00122Q002C00E36Q002D3Q000B00122Q002E00C13Q00202Q002E002E00C200122Q002F00E43Q00122Q003000E56Q002E0030000200102Q002D00C0002E00122Q002E00C13Q00202Q002E002E008800122Q002F00293Q00122Q003000E63Q00122Q003100C83Q00122Q003200E76Q002E0032000200102Q002D00C3002E00202Q002E0018009C00102Q002D00C6002E00302Q002D00D6001600302Q002D00E800E900202Q002E001800A400102Q002D00EA002E00202Q002E001800A100102Q002D00D9002E00122Q002E008F3Q00202Q002E002E00DA00202Q002E002E00E200102Q002D00DA002E00302Q002D00DC003100302Q002D00EB002500122Q002E008F3Q0020E3002E002E00DD0020E3002E002E00DE00105D012D00DD002E2Q0046012E00284Q00FC002B002E00022Q0046012C001A4Q0046012D002B3Q001216002E00D54Q00EE002C002E00012Q0046012C00193Q001216002D00EC4Q0013012E3Q0001001288012F00EE3Q0020E3002F002F0088001216003000C83Q0012160031001D4Q00FC002F0031000200105D012E00ED002F2Q0046012F002B4Q00EE002C002F00010006B7002C0010000100042Q0046012Q00194Q0046012Q00184Q0046012Q00284Q0046012Q001A4Q0046012D002C3Q001216002E00EF3Q001216002F00F04Q00FC002D002F00022Q0046012E002C3Q001216002F00F13Q001216003000F24Q00FC002E003000022Q0046012F002C3Q001216003000F33Q001216003100F43Q00124F003200AA6Q002F0032000200202Q0030002D00F500202Q0030003000F64Q003200226Q0030003200014Q003000193Q00122Q003100BF6Q00323Q000400122Q003300C13Q0020E3003300330088001216003400293Q001216003500F73Q001216003600C83Q001216003700294Q00FC00330037000200105D013200C00033001288013300C13Q0020E30033003300C20012160034001D3Q001216003500CF4Q00FC00330035000200105D013200C300330020E300330018009E00105D013200C60033003093003200C700C82Q0046013300274Q00EE0030003300010006B700300011000100012Q0046012Q00273Q0020E30031002E00F500208D0031003100F62Q0046013300304Q00EE0031003300012Q0046013100213Q0020E30032000200F800208D0032003200F60006B700340012000100012Q0046012Q00304Q00A1013200344Q00F700313Q00012Q00E700316Q0062003200333Q0020E30034002800F800208D0034003400F60006B700360013000100052Q0046012Q001B4Q0046012Q00314Q0046012Q00324Q0046012Q00334Q0046012Q00274Q00EE0034003600012Q0046013400213Q0020E30035000200F900208D0035003500F60006B700370014000100052Q0046012Q00314Q0046012Q001C4Q0046012Q00324Q0046012Q00274Q0046012Q00334Q0068013500376Q00343Q00014Q003400213Q00202Q0035000200FA00202Q0035003500F60006B700370015000100022Q0046012Q001B4Q0046012Q00314Q00B4003500376Q00343Q00014Q00318Q003100193Q00122Q003200FB6Q00333Q000700122Q003400C13Q00202Q0034003400C200122Q003500CF3Q00122Q003600CF6Q00340036000200102Q003300C0003400122Q003400C13Q00202Q00340034008800122Q003500C83Q00122Q003600D43Q00122Q003700C43Q00122Q003800FC6Q00340038000200102Q003300C3003400122Q003400953Q00202Q00340034009600122Q003500D53Q00122Q0036001D3Q00122Q003700D36Q00340037000200102Q003300C6003400302Q003300D6001600302Q003300FD002500302Q003300FE007300302Q003300FF00234Q003400166Q0031003400024Q0032001A6Q003300313Q00122Q00342Q00015Q0032003400014Q003200193Q00122Q003300C96Q00343Q000200122Q003500C53Q00102Q003400CA003500202Q0035001800AB00102Q003400CC00354Q003500316Q0032003500014Q003200193Q00122Q0033002Q015Q00343Q000200122Q00350002012Q00202Q00350035008800122Q003600953Q00202Q00360036009600122Q00370003012Q00122Q00380004012Q00122Q00390005015Q00360039000200122Q003700953Q00202Q00370037009600122Q003800383Q00122Q00390006012Q00122Q003A0007015Q0037003A6Q00353Q000200102Q003400CC003500122Q00350008012Q00122Q0036002F6Q0034003500364Q003500316Q0032003500014Q003200193Q00122Q003300BF6Q00343Q000300122Q003500C13Q00202Q00350035008800122Q003600293Q00122Q003700C83Q00122Q003800293Q00122Q003900C86Q00350039000200105D013400C00035001216003500293Q00105D013400D0003500121600350009012Q00105D013400FE00352Q0046013500314Q00FC003200350002001216003300CF4Q001301343Q000800129A0035000A015Q003600023Q00122Q003700C43Q00122Q0038000B015Q0036000200012Q009E00340035003600129A0035000C015Q003600023Q00122Q0037000D012Q00122Q0038000E015Q0036000200012Q009E00340035003600129A0035000F015Q003600023Q00122Q00370010012Q00122Q0038000E015Q0036000200012Q009E00340035003600129A00350011015Q003600023Q00122Q00370012012Q00122Q00380013015Q0036000200012Q009E00340035003600129A00350014015Q003600023Q00122Q00370015012Q00122Q00380016015Q0036000200012Q009E00340035003600129A00350017015Q003600023Q00122Q00370018012Q00122Q00380019015Q0036000200012Q009E00340035003600129A0035001A015Q003600023Q00122Q0037001B012Q00122Q0038001C015Q0036000200012Q009E00340035003600129A0035001D015Q003600023Q00122Q0037001E012Q00122Q0038001F015Q0036000200012Q009E0034003500360006B700350016000100022Q0046012Q00344Q0046012Q00333Q0006B700360017000100032Q0046012Q00354Q0046012Q00194Q0046012Q00323Q00128801370020013Q0013013800084Q0013013900023Q001216003A000C012Q001216003B000A013Q00230139000200012Q0013013A00023Q001216003B000A012Q001216003C000F013Q0023013A000200012Q0013013B00023Q001216003C000C012Q001216003D0017013Q0023013B000200012Q0013013C00023Q001216003D000F012Q001216003E0011013Q0023013C000200012Q0013013D00023Q001216003E0017012Q001216003F0014013Q0023013D000200012Q0013013E00023Q001216003F0014012Q00121600400011013Q0023013E000200012Q0013013F00023Q00121600400017012Q0012160041001A013Q0023013F000200012Q0013014000023Q00121600410011012Q0012160042001D013Q00230140000200012Q00230138000800012Q00B200370002003900040F012Q00FC02012Q0046013C00363Q0012C4003D00296Q003D003B003D00122Q003E00C56Q003E003B003E4Q003C003E000100062B003700F60201000200040F012Q00F602010006B700370018000100042Q0046012Q00354Q0046012Q00194Q0046012Q00324Q0046012Q001A4Q00F4003800373Q00122Q0039000C012Q00122Q003A00673Q00122Q003B00953Q00202Q003B003B009600122Q003C0021012Q00122Q003D0022012Q00122Q003E0023015Q003B003E6Q00383Q00014Q003800373Q00122Q0039001D012Q00122Q003A00673Q00122Q003B00953Q00202Q003B003B009600122Q003C0024012Q00122Q003D0025012Q00122Q003E0021015Q003B003E6Q00383Q00014Q003800373Q00122Q0039000F012Q00122Q003A0026012Q00122Q003B00953Q00202Q003B003B009600122Q003C0022012Q00122Q003D0024012Q00122Q003E0021015Q003B003E6Q00383Q00014Q003800373Q00122Q0039000A012Q00122Q003A0026012Q00122Q003B00953Q00202Q003B003B009600122Q003C0022012Q00122Q003D0024012Q00122Q003E0021015Q003B003E6Q00383Q00014Q003800373Q00122Q00390011012Q00122Q003A0026012Q00122Q003B00953Q00202Q003B003B009600122Q003C00193Q00122Q003D0027012Q00122Q003E0021015Q003B003E6Q00383Q00014Q003800373Q00122Q00390014012Q00122Q003A0026012Q00122Q003B00953Q00202Q003B003B009600122Q003C00193Q00122Q003D0027012Q00122Q003E0021015Q003B003E6Q00383Q00014Q003800373Q00122Q00390017012Q00122Q003A0026012Q00122Q003B00953Q00202Q003B003B009600122Q003C00193Q00122Q003D0027012Q00122Q003E0021015Q003B003E6Q00383Q00014Q003800373Q00122Q0039001A012Q00122Q003A0026012Q00122Q003B00953Q00202Q003B003B009600122Q003C0022012Q00122Q003D0024012Q00122Q003E0021015Q003B003E6Q00383Q000100267B0010005F0301001600040F012Q005F030100128801380028012Q00121600390029013Q00730038003800390006B700390019000100052Q0046012Q00104Q0046012Q00194Q0046012Q00314Q0046012Q001A4Q0046012Q00324Q00330038000200012Q00E700386Q00E700396Q0062003A003B3Q0020E3003C003100F800208D003C003C00F60006B7003E001A000100062Q0046012Q001B4Q0046012Q00384Q0046012Q00394Q0046012Q003A4Q0046012Q003B4Q0046012Q00314Q00EE003C003E00012Q0046013C00213Q0020E3003D000200F900208D003D003D00F60006B7003F001B000100062Q0046012Q00384Q0046012Q001C4Q0046012Q003A4Q0046012Q00394Q0046012Q00314Q0046012Q003B4Q0068013D003F6Q003C3Q00014Q003C00213Q00202Q003D000200FA00202Q003D003D00F60006B7003F001C000100042Q0046012Q00384Q0046012Q001B4Q0046012Q00394Q0046012Q00304Q00A1013D003F4Q00F7003C3Q00012Q000F00316Q0046013100193Q00121E0032002A015Q00333Q000700122Q003400C13Q00202Q00340034008800122Q003500C83Q00122Q003600A53Q00122Q003700293Q00122Q0038002B015Q00340038000200102Q003300C00034001288013400C13Q0020E30034003400C20012160035001D3Q0012160036002C013Q00FC00340036000200105D013300C30034001216003400293Q00105D013300D00034001216003400C83Q00105D013300C700340012160034002D012Q001216003500C84Q009E0033003400350012160034002E012Q001288013500C13Q0020E30035003500882Q00650135000100022Q009E0033003400350012160034002F012Q0012880135008F3Q00121600360030013Q00730035003500360020E30035003500BE2Q009E0033003400352Q0046013400274Q00FC0031003400022Q0046013200193Q00121600330031013Q001301343Q000100121600350032012Q001288013600EE3Q0020E3003600360088001216003700C83Q00121600380026013Q00FC0036003800022Q009E0034003500362Q0046013500314Q00EE0032003500012Q0046013200193Q00121E003300BF6Q00343Q000300122Q003500C13Q00202Q00350035008800122Q003600293Q00122Q00370033012Q00122Q003800293Q00122Q00390034015Q00350039000200102Q003400C00035001288013500C13Q0020E30035003500C200121600360035012Q0012160037002C013Q00FC00350037000200105D013400C30035001216003500293Q00105D013400D000352Q0046013500274Q00FC0032003500022Q001301336Q0062003400343Q0006B70035001D000100032Q0046012Q00344Q0046012Q00334Q0046012Q00184Q001301366Q001301375Q0006B70038001E000100012Q0046012Q00373Q0006B70039001F000100022Q0046012Q00364Q0046012Q00123Q0006B7003A0020000100042Q0046012Q00194Q0046012Q00184Q0046012Q001A4Q0046012Q00013Q0006B7003B0021000100102Q0046012Q00194Q0046012Q00184Q0046012Q00314Q0046012Q001A4Q0046012Q00324Q0046012Q00334Q0046012Q00354Q0046012Q00124Q0046012Q00144Q0046012Q00364Q0046012Q003A4Q0046012Q00374Q0046012Q001B4Q0046012Q00214Q0046012Q00024Q0046012Q001C3Q0006B7003C0022000100022Q0046012Q00344Q0046012Q002B3Q001216003F0036013Q0090013D002B003F001216003F00D64Q00FC003D003F000200208D003D003D00F62Q0046013F003C4Q00EE003D003F00012Q0046013D003B3Q001216003E0037013Q009C013D000200022Q0046013E003B3Q001216003F0038013Q009C013E000200022Q0046013F003B3Q00121600400039013Q009C013F000200022Q00460140003B3Q0012160041003A013Q009C0140000200022Q00460141003B3Q0012160042003B013Q009C0141000200022Q00460142003B3Q0012160043003C013Q009C0142000200022Q00460143003B3Q0012160044003D013Q009C0143000200022Q00460144003B3Q0012160045003E013Q009C0144000200022Q00460145003B3Q0012160046003F013Q009C0145000200022Q00460146003B3Q00121600470040013Q009C0146000200022Q00460147003B3Q00121600480041013Q009C0147000200022Q00460148003B3Q00121600490042013Q009C0148000200020020E30049002F00F500208D0049004900F60006B7004B0023000100022Q0046012Q00354Q0046012Q003D4Q00EE0049004B000100128801490043012Q001216004A0044013Q007300490049004A2Q00650149000100022Q0062004A004A3Q001288014B0028012Q001216004C0029013Q0073004B004B004C0006B7004C0024000100042Q0046012Q001D4Q0046012Q00164Q0046012Q00494Q0046012Q004A4Q0033004B000200010006B7004B0025000100012Q0046012Q000C3Q0006B7004C0026000100012Q0046012Q000C3Q0006B7004D0027000100012Q0046012Q00043Q0006B7004E0028000100012Q0046012Q004D3Q0006B7004F0029000100012Q0046012Q000C3Q0002850050002A4Q006A00513Q000300122Q00520045012Q00122Q005300296Q00510052005300122Q00520046012Q00122Q005300C56Q00510052005300122Q00520047012Q00122Q00530026015Q005100520053001288015200013Q00121600530048013Q00730052005200532Q00730051005100520006570151004A0401000100040F012Q004A0401001216005100C83Q0006B70052002B000100022Q0046012Q00514Q0046012Q000C3Q0002850053002C3Q0002850054002D3Q0006B70055002E000100022Q0046012Q00544Q0046012Q00503Q001216005600C83Q0006B70057002F000100062Q0046012Q00564Q0046012Q004C4Q0046012Q00124Q0046012Q00014Q0046012Q001D4Q0046012Q00033Q0006B700580030000100012Q0046012Q00123Q001216005900C83Q0006B7005A0031000100032Q0046012Q004C4Q0046012Q00594Q0046012Q00124Q0046015B00213Q001216005C0049013Q0073005C0003005C00208D005C005C00F60006B7005E0032000100042Q0046012Q00124Q0046012Q001E4Q0046012Q001F4Q0046012Q000C4Q00A1015C005E4Q00F7005B3Q0001001216005B00C83Q0006B7005C0033000100042Q0046012Q00124Q0046012Q005B4Q0046012Q000C4Q0046012Q004E3Q0006B7005D0034000100022Q0046012Q000C4Q0046012Q004B3Q0006B7005E0035000100032Q0046012Q005C4Q0046012Q005D4Q0046012Q00123Q000285005F00363Q0006B700600037000100012Q0046012Q00273Q0006B700610038000100042Q0046012Q000D4Q0046012Q005F4Q0046012Q00604Q0046012Q00053Q0006B700620039000100012Q0046012Q000C4Q0062006300633Q00128801640028012Q00121600650029013Q00730064006400650006B70065003A000100022Q0046012Q000C4Q0046012Q00634Q00330064000200010006B70064003B000100012Q0046012Q00633Q0006B70065003C000100012Q0046012Q00643Q0006B70066003D000100012Q0046012Q00643Q0006B70067003E000100012Q0046012Q00044Q0062006800683Q0006B70069003F000100022Q0046012Q00684Q0046012Q00503Q0006B7006A0040000100022Q0046012Q004C4Q0046012Q00693Q0006B7006B0041000100032Q0046012Q00674Q0046012Q006A4Q0046012Q00694Q007F006C00053Q00122Q006D004A012Q00122Q006E004B012Q00122Q006F004C012Q00122Q0070004D012Q00122Q0071004E015Q006C000500012Q0013016D3Q0005001216006E004A012Q001216006F004A013Q009E006D006E006F001216006E004F012Q001216006F004B013Q009E006D006E006F001216006E0050012Q001216006F004C013Q009E006D006E006F001216006E004D012Q001216006F004D013Q009E006D006E006F001216006E004E012Q001216006F004E013Q009E006D006E006F2Q0013016E3Q0005001216006F0051012Q001216007000294Q009E006E006F0070001216006F0052013Q0062007000704Q009E006E006F0070001216006F0053012Q001216007000C84Q009E006E006F0070001216006F0054012Q001216007000C84Q009E006E006F0070001216006F0055013Q00E700706Q009E006E006F00702Q0062006F00704Q001301713Q00010012A100720056015Q00738Q00710072007300122Q00720028012Q00122Q00730029015Q0072007200730006B700730042000100022Q0046012Q00044Q0046012Q00714Q00330072000200012Q0062007200723Q001216007300C83Q0006B700740043000100032Q0046012Q00724Q0046012Q00734Q0046012Q000C3Q0006B700750044000100022Q0046012Q00744Q0046012Q00123Q0006B700760045000100012Q0046012Q000C3Q0006B700770046000100042Q0046012Q00764Q0046012Q00694Q0046017Q0046012Q00123Q0006B700700047000100022Q0046012Q00714Q0046012Q000C3Q0006B7006F0048000100062Q0046012Q00704Q0046012Q000C4Q0046012Q00754Q0046012Q00774Q0046012Q00124Q0046012Q00713Q0012C6007800C86Q007900213Q00122Q007A0057015Q007A0003007A00202Q007A007A00F60006B7007C0049000100072Q0046012Q001D4Q0046012Q00124Q0046012Q001E4Q0046012Q001F4Q0046012Q006E4Q0046012Q00784Q0046012Q006F4Q00A1017A007C4Q00F700793Q00012Q000F00716Q0046017100213Q00121600720057013Q007300720003007200208D0072007200F60006B70074004A000100082Q0046012Q001D4Q0046012Q00124Q0046012Q001E4Q0046012Q001F4Q0046012Q006F4Q0046012Q006B4Q0046012Q00684Q0046012Q00654Q00A1017200744Q00F700713Q00010006B70071004B000100072Q0046012Q00684Q0046012Q00704Q0046012Q00654Q0046012Q00664Q0046012Q006B4Q0046012Q00624Q0046012Q00613Q0006B70072004C0001000A2Q0046012Q00124Q0046012Q00684Q0046012Q006B4Q0046012Q00624Q0046012Q00614Q0046012Q006C4Q0046012Q006E4Q0046012Q00704Q0046012Q00714Q0046012Q006D3Q0006B70073004D000100032Q0046012Q00124Q0046012Q006E4Q0046012Q006C3Q0006B70074004E000100032Q0046012Q00124Q0046012Q006C4Q0046012Q006E3Q0006B70075004F000100022Q0046012Q00124Q0046012Q006E3Q0006B700760050000100032Q0046012Q00124Q0046012Q000D4Q0046012Q000A3Q0006B700770051000100022Q0046012Q000D4Q0046012Q00763Q0006B700780052000100012Q0046012Q00533Q0006B700790053000100022Q0046012Q00504Q0046012Q00783Q0006B7007A0054000100012Q0046012Q004C3Q0006B7007B00550001000B2Q0046012Q004C4Q0046012Q006E4Q0046012Q00584Q0046012Q00574Q0046012Q005E4Q0046012Q005D4Q0046012Q00124Q0046012Q005A4Q0046012Q00724Q0046012Q00734Q0046012Q00773Q0006B7007C0056000100012Q0046012Q00504Q0013017D5Q0006B7007E0057000100042Q0046012Q004C4Q0046012Q007C4Q0046012Q00534Q0046012Q007D3Q0006B7007F0058000100052Q0046012Q004C4Q0046012Q007E4Q0046012Q00574Q0046012Q00124Q0046012Q00553Q000285008000593Q0002850081005A4Q00E700826Q00E700836Q001301846Q0046018500213Q00121600860058013Q007300860008008600208D0086008600F60006B70088005B000100022Q0046012Q00824Q0046012Q00834Q00A1018600884Q00F700853Q00010006B70085005C000100072Q0046012Q00824Q0046012Q00814Q0046012Q00074Q0046012Q00844Q0046012Q00834Q0046012Q00084Q0046012Q000C4Q001301863Q000300121600870059013Q001301886Q009E0086008700880012160087005A013Q001301886Q009E0086008700880012160087005B013Q001301886Q009E0086008700880006B70087005D000100012Q0046012Q00863Q0006B70088005E000100012Q0046012Q00123Q0006B70089005F000100022Q0046012Q00864Q0046012Q00883Q0006B7008A0060000100082Q0046012Q001D4Q0046012Q00164Q0046012Q00864Q0046012Q00884Q0046012Q00684Q0046012Q001E4Q0046012Q00894Q0046012Q00384Q0062008B008D3Q0006B7008B0061000100012Q0046012Q000C3Q000285008C00623Q000285008E00633Q0006B7008F0064000100012Q0046012Q000A3Q0006B700900065000100032Q0046012Q000D4Q0046012Q008F4Q0046012Q00603Q0006B700910066000100042Q0046012Q000C4Q0046012Q00164Q0046012Q008C4Q0046012Q008E3Q0006B7008D0067000100022Q0046012Q00914Q0046012Q00904Q000F008E6Q0062008E008E3Q0006B7008F0068000100022Q0046012Q008E4Q0046012Q00043Q0006B700900069000100012Q0046012Q00503Q0002850091006A4Q0062009200923Q0006B70093006B000100082Q0046012Q008F4Q0046012Q00524Q0046012Q00514Q0046012Q00504Q0046012Q004C4Q0046012Q00904Q0046012Q00924Q0046012Q00913Q0002850094006C3Q0006B70095006D000100032Q0046017Q0046012Q00944Q0046012Q00503Q0006B70096006E000100012Q0046012Q008B3Q0006B70097006F000100042Q0046012Q000C4Q0046012Q00504Q0046012Q00164Q0046012Q008C3Q0006B700980070000100042Q0046012Q000C4Q0046012Q00504Q0046012Q00164Q0046012Q008C3Q0006B700990071000100012Q0046012Q00973Q0006B700920072000100012Q0046012Q00503Q0006B7009A0073000100032Q0046012Q004C4Q0046012Q00914Q0046012Q00943Q001216009B00C83Q001216009C00163Q0006B7009D0074000100092Q0046012Q009A4Q0046012Q009B4Q0046012Q009C4Q0046012Q007F4Q0046012Q004C4Q0046012Q00674Q0046012Q004E4Q0046012Q00804Q0046012Q008D3Q0006B7009E0075000100032Q0046012Q004C4Q0046012Q00574Q0046012Q00123Q0006B7009F0076000100152Q0046012Q00684Q0046012Q004C4Q0046012Q00924Q0046012Q00914Q0046012Q009A4Q0046012Q009D4Q0046012Q00904Q0046012Q00554Q0046012Q009E4Q0046012Q00574Q0046012Q00584Q0046012Q00124Q0046012Q005E4Q0046012Q00754Q0046012Q005D4Q0046012Q00984Q0046012Q00994Q0046012Q00744Q0046012Q005A4Q0046012Q00724Q0046012Q00734Q001D01A05Q00122Q00A1005C012Q00122Q00A2005D015Q00A100A100A200122Q00A2005B015Q00A2008600A20006B700A30077000100012Q0046012Q00A04Q00EE00A100A300010006B700A10078000100132Q0046012Q00A04Q0046012Q004F4Q0046012Q00934Q0046012Q00964Q0046012Q00974Q0046012Q004E4Q0046012Q00994Q0046012Q00914Q0046012Q009A4Q0046012Q009D4Q0046012Q00904Q0046012Q004C4Q0046012Q00554Q0046012Q00924Q0046012Q00954Q0046012Q00574Q0046012Q00124Q0046012Q009E4Q0046012Q009F4Q006200A200A24Q001301A33Q000500121600A4005E013Q00E700A500014Q009E00A300A400A500121600A4005F013Q00E700A500014Q009E00A300A400A500121600A40060013Q00E700A500014Q009E00A300A400A500125D00A40061015Q00A500016Q00A300A400A500122Q00A40062015Q00A500016Q00A300A400A54Q00A43Q000400122Q00A50063015Q00A600016Q00A400A500A600121600A50064013Q00E700A600014Q009E00A400A500A600121600A50065013Q00E700A600014Q009E00A400A500A600121600A50066013Q00E700A600014Q009E00A400A500A600121600A500C83Q0006B700A60079000100062Q0046012Q00124Q0046012Q00794Q0046012Q007A4Q0046012Q007B4Q0046012Q00A54Q0046012Q004E3Q00028500A2007A4Q004601A700873Q00121600A800413Q00121600A9002F4Q004601AA00A23Q0006B700AB007B000100012Q0046012Q00A14Q000E00A700AB00014Q00A700873Q00122Q00A800433Q00122Q00A9002F6Q00AA00A23Q0006B700AB007C000100022Q0046012Q00A14Q0046012Q00A34Q000E00A700AB00014Q00A700873Q00122Q00A800443Q00122Q00A9002F6Q00AA00A23Q0006B700AB007D000100032Q0046012Q00A14Q0046012Q00A64Q0046012Q00A44Q000E00A700AB00014Q00A700873Q00122Q00A800453Q00122Q00A9002F6Q00AA00A23Q0006B700AB007E000100022Q0046012Q00A14Q0046012Q00A44Q00EE00A700AB00012Q000F00A35Q0006B700A3007F0001000A2Q0046012Q00794Q0046012Q007A4Q0046012Q00744Q0046012Q007B4Q0046012Q00124Q0046012Q00044Q0046012Q00504Q0046012Q00534Q0046012Q004C4Q0046012Q009E3Q00126700A400C86Q00A500873Q00122Q00A600473Q00122Q00A70067015Q00A800A23Q0006B700A90080000100082Q0046012Q00524Q0046012Q00514Q0046012Q00A34Q0046012Q00A44Q0046012Q007F4Q0046012Q004E4Q0046012Q00804Q0046012Q008D4Q00EE00A500A900010006B700A50081000100062Q0046012Q00874Q0046012Q00794Q0046012Q007A4Q0046012Q00744Q0046012Q007B4Q0046012Q00124Q004601A600A53Q00121600A700484Q001301A800013Q00121600A90068013Q002301A80001000100121600A90069013Q00EE00A600A900012Q004601A600A53Q00121600A7004B4Q001301A800013Q00121600A9006A013Q002301A80001000100121600A9006B013Q00EE00A600A900012Q004601A600A53Q00121600A7004D4Q001301A800013Q00121600A9006C013Q002301A80001000100121600A9006D013Q00EE00A600A900012Q006200A600A73Q0006B700A60082000100022Q0046012Q000C4Q0046012Q00503Q0006B700A70083000100012Q0046012Q004B3Q0006B700A80084000100022Q0046012Q004C4Q0046012Q00503Q0006B700A900850001000A2Q0046012Q00874Q0046012Q00124Q0046012Q00524Q0046012Q00514Q0046012Q00394Q0046012Q00A64Q0046012Q00554Q0046012Q00574Q0046012Q00A74Q0046012Q00A84Q004601AA00A93Q00121600AB00494Q001301AC3Q000700121600AD006E012Q00121600AE0026013Q009E00AC00AD00AE00121600AD006F013Q001301AE00013Q00121600AF0070013Q002301AE000100012Q009E00AC00AD00AE00121600AD0071012Q00121600AE0072013Q009E00AC00AD00AE00129A00AD0073015Q00AE00023Q00122Q00AF0074012Q00122Q00B00075015Q00AE000200012Q009E00AC00AD00AE00121600AD0076012Q00121600AE0077013Q009E00AC00AD00AE00121600AD0078013Q007F00AE00053Q00122Q00AF0079012Q00122Q00B0007A012Q00122Q00B1007B012Q00122Q00B2007C012Q00122Q00B3007D015Q00AE000500012Q009E00AC00AD00AE0012CE00AD007E012Q00122Q00AE007F015Q00AC00AD00AE4Q00AA00AC00014Q00AA00A93Q00122Q00AB004C6Q00AC3Q000700122Q00AD006E012Q00122Q00AE0026015Q00AC00AD00AE00121600AD006F013Q001301AE00013Q00121600AF0080013Q002301AE000100012Q009E00AC00AD00AE00121600AD0071012Q00121600AE0081013Q009E00AC00AD00AE00129A00AD0073015Q00AE00023Q00122Q00AF0082012Q00122Q00B00083015Q00AE000200012Q009E00AC00AD00AE00125A01AD0076012Q00122Q00AE0084015Q00AC00AD00AE00122Q00AD0078015Q00AE00043Q00122Q00AF007C012Q00122Q00B0007B012Q00122Q00B10085012Q00122Q00B20079015Q00AE000400012Q009E00AC00AD00AE0012CE00AD007E012Q00122Q00AE0086015Q00AC00AD00AE4Q00AA00AC00014Q00AA00A93Q00122Q00AB004E6Q00AC3Q000700122Q00AD006E012Q00122Q00AE00C56Q00AC00AD00AE00121600AD006F013Q001301AE00013Q00121600AF0087013Q002301AE000100012Q009E00AC00AD00AE00121600AD0071012Q00121600AE0088013Q009E00AC00AD00AE00129A00AD0073015Q00AE00023Q00122Q00AF0089012Q00122Q00B0008A015Q00AE000200012Q009E00AC00AD00AE00125A01AD0076012Q00122Q00AE008B015Q00AC00AD00AE00122Q00AD0078015Q00AE00043Q00122Q00AF0079012Q00122Q00B0007C012Q00122Q00B1007B012Q00122Q00B2008C015Q00AE000400012Q009E00AC00AD00AE00121600AD007E012Q00121600AE008D013Q009E00AC00AD00AE2Q00EE00AA00AC00012Q004601AA00873Q00121600AB004A3Q00121600AC0004012Q0006B700AD0086000100012Q0046012Q00123Q0006B700AE0087000100072Q0046012Q00524Q0046012Q00514Q0046012Q00394Q0046012Q00554Q0046012Q00574Q0046012Q00124Q0046012Q00A84Q005500AA00AE00014Q00A88Q00A800873Q00122Q00A9004F3Q00122Q00AA008E015Q00AB00A23Q0006B700AC0088000100042Q0046012Q00A34Q0046012Q00124Q0046012Q00794Q0046012Q00854Q002000A800AC00014Q00A800A86Q00A900076Q00AA3Q000300122Q00AB008F012Q00202Q00AA00AB005000122Q00AB0090012Q00122Q00AC0091015Q00AA00AB00AC00122Q00AB0092013Q001301AC00013Q00121600AD0093013Q002301AC000100012Q009E00AA00AB00AC2Q000500AB3Q000400122Q00AC008F012Q00202Q00AB00AC005100122Q00AC0090012Q00122Q00AD0094015Q00AB00AC00AD00122Q00AC0092015Q00AD00013Q00122Q00AE0093015Q00AD000100012Q009E00AB00AC00AD00121600AC0095013Q00E700AD00014Q009E00AB00AC00AD2Q000500AC3Q000300122Q00AD008F012Q00202Q00AC00AD005200122Q00AD0090012Q00122Q00AE0096015Q00AC00AD00AE00122Q00AD0092015Q00AE00013Q00122Q00AF0097015Q00AE000100012Q009E00AC00AD00AE2Q000500AD3Q000300122Q00AE008F012Q00202Q00AD00AE005300122Q00AE0090012Q00122Q00AF0098015Q00AD00AE00AF00122Q00AE0092015Q00AF00013Q00122Q00B00099015Q00AF000100012Q009E00AD00AE00AF2Q000500AE3Q000300122Q00AF008F012Q00202Q00AE00AF005400122Q00AF0090012Q00122Q00B0009A015Q00AE00AF00B000122Q00AF0092015Q00B000013Q00122Q00B1009B015Q00B0000100012Q009E00AE00AF00B02Q000500AF3Q000300122Q00B0008F012Q00202Q00AF00B0005500122Q00B00090012Q00122Q00B1009C015Q00AF00B000B100122Q00B00092015Q00B100013Q00122Q00B2009D015Q00B1000100012Q009E00AF00B000B12Q001301B03Q000300121600B1008F012Q00202C00B000B1005600121600B10090012Q00121600B2009E013Q009E00B000B100B200121600B10092013Q001301B200073Q00121600B3009F012Q00121600B400A0012Q00121600B500A1012Q00121C00B600A2012Q00122Q00B700A3012Q00122Q00B800A4012Q00122Q00B900A5015Q00B2000700012Q009E00B000B100B22Q002301A9000700012Q004601A800A93Q0006B700A90089000100032Q0046012Q00794Q0046012Q00504Q0046012Q00533Q0006B700AA008A000100042Q0046012Q00A84Q0046012Q00124Q0046012Q00A94Q0046012Q00794Q004601AB00873Q00121600AC006E012Q00121600AD00A6012Q0006B700AE008B000100012Q0046012Q00AA3Q0006B700AF008C000100052Q0046012Q00AA4Q0046012Q007A4Q0046012Q00744Q0046012Q007B4Q0046012Q00123Q0006B700B0008D000100022Q0046012Q00A84Q0046012Q00124Q00EE00AB00B000012Q000F00A96Q006200A900B03Q00028500A9008E3Q00028500B1008F3Q0006B700AA0090000100012Q0046012Q00B13Q0006B700AB0091000100012Q0046012Q004C4Q001301B23Q000700121600B300A7013Q001301B46Q009E00B200B300B400121600B300A8013Q001301B46Q009E00B200B300B400121600B300A9013Q001301B46Q009E00B200B300B400121600B300AA013Q001301B46Q009E00B200B300B400121600B300AB013Q00E700B46Q009E00B200B300B400121600B300AC012Q00121600B400C84Q009E00B200B300B400121600B300AD013Q006200B400B44Q009E00B200B300B40006B700B30092000100022Q0046012Q00A94Q0046012Q00B23Q0006B700B40093000100022Q0046012Q00AC4Q0046012Q00B23Q00028500B500943Q00028500B000953Q0006B700AF0096000100022Q0046012Q000C4Q0046012Q00B53Q0006B700AD0097000100042Q0046012Q00B24Q0046012Q00AF4Q0046012Q00B04Q0046012Q00A93Q0006B700AE0098000100042Q0046012Q004E4Q0046012Q00A94Q0046012Q00B24Q0046012Q00B43Q0006B700B60099000100062Q0046012Q004D4Q0046012Q00AF4Q0046012Q00B04Q0046012Q00B34Q0046012Q00B24Q0046012Q00AE3Q0006B700B7009A000100042Q0046012Q004C4Q0046012Q00AA4Q0046012Q00B24Q0046012Q00B33Q0012D800B8005C012Q00122Q00B9005D015Q00B800B800B900122Q00B9005B015Q00B9008600B90006B700BA009B000100012Q0046012Q00B24Q00EE00B800BA00012Q001301B8000E3Q00125201B900413Q00122Q00BA00423Q00122Q00BB00433Q00122Q00BC00443Q00122Q00BD00453Q00122Q00BE00473Q00122Q00BF004F3Q00122Q00C000593Q00122Q00C1005A3Q00122Q00C2007B3Q00121C00C3007C3Q00122Q00C4007D3Q00122Q00C5005B3Q00122Q00C6005C6Q00B8000E00010006B700B9009C000100022Q0046012Q00B84Q0046012Q00124Q004601BA00873Q00121600BB00573Q00121600BC001D3Q0006B700BD009D000100032Q0046012Q00B74Q0046012Q00124Q0046012Q00B93Q0006B700BE009E0001000B2Q0046012Q00B24Q0046012Q00AD4Q0046012Q00AE4Q0046012Q00B74Q0046012Q00124Q0046012Q00B64Q0046012Q00854Q0046012Q00574Q0046012Q00AF4Q0046012Q004C4Q0046012Q00AB4Q00EE00BA00BE00012Q000F00B16Q006200B100B14Q006A00B23Q000300122Q00B300AE012Q00122Q00B400AF015Q00B200B300B400122Q00B300B0012Q00122Q00B400B1015Q00B200B300B400122Q00B300B2012Q00122Q00B400B3015Q00B200B300B400028500B3009F3Q0006B700B100A0000100042Q0046012Q00534Q0046012Q00B34Q0046012Q00B24Q0046012Q00063Q0006B700B400A1000100012Q0046012Q004C3Q0006B700B500A2000100012Q0046012Q000C3Q0006B700B600A3000100022Q0046012Q00544Q0046012Q00913Q0006B700B700A4000100012Q0046012Q000C3Q0006B700B800A5000100032Q0046012Q004C4Q0046012Q00574Q0046012Q00124Q001301B93Q000200121600BA00B4013Q001301BB6Q009E00B900BA00BB00121600BA00B5013Q001301BB6Q009E00B900BA00BB0012D800BA005C012Q00122Q00BB005D015Q00BA00BA00BB00122Q00BB005B015Q00BB008600BB0006B700BC00A6000100012Q0046012Q00B94Q00EE00BA00BC000100028500BA00A74Q004601BB00873Q00121600BC00423Q00121600BD00AA4Q004601BE00A23Q0006B700BF00A80001000C2Q0046012Q004C4Q0046012Q00B14Q0046012Q00B94Q0046012Q00BA4Q0046012Q00B84Q0046012Q00B54Q0046012Q00574Q0046012Q00124Q0046012Q00B44Q0046012Q00B34Q0046012Q00B64Q0046012Q00B74Q00EE00BB00BF00012Q000F00B26Q001301B23Q000100121600B300B6012Q00121600B400294Q009E00B200B300B40012D800B3005C012Q00122Q00B4005D015Q00B300B300B400122Q00B4005B015Q00B4008600B40006B700B500A9000100012Q0046012Q00B24Q000E00B300B500014Q00B300873Q00122Q00B400593Q00122Q00B500736Q00B600A23Q0006B700B700AA0001000B2Q0046012Q00524Q0046012Q00514Q0046012Q004F4Q0046012Q004E4Q0046012Q00B24Q0046012Q00394Q0046012Q00A34Q0046012Q00994Q0046012Q009F4Q0046012Q007F4Q0046012Q00804Q000E00B300B700014Q00B300873Q00122Q00B4005A3Q00122Q00B500736Q00B600A23Q0006B700B700AB000100082Q0046012Q00524Q0046012Q00514Q0046012Q004F4Q0046012Q00A34Q0046012Q007F4Q0046012Q004E4Q0046012Q00804Q0046012Q008D4Q00EE00B300B700012Q001301B33Q000200121600B400B7012Q00121600B500C84Q009E00B300B400B500121600B400B6012Q00202C00B300B400160012D800B4005C012Q00122Q00B5005D015Q00B400B400B500122Q00B5005B015Q00B5008600B50006B700B600AC000100012Q0046012Q00B34Q000E00B400B600014Q00B400873Q00122Q00B5007B3Q00122Q00B600736Q00B700A23Q0006B700B800AD000100142Q0046012Q00524Q0046012Q00514Q0046012Q004F4Q0046012Q00124Q0046012Q00144Q0046012Q00B34Q0046012Q000C4Q0046012Q00794Q0046012Q00A34Q0046012Q004C4Q0046012Q009E4Q0046012Q00574Q0046012Q00AB4Q0046012Q004E4Q0046012Q00554Q0046012Q00804Q0046012Q000D4Q0046012Q008D4Q0046017Q0046012Q00504Q00EE00B400B8000100121600B400C83Q00126700B500C86Q00B600873Q00122Q00B7007C3Q00122Q00B800736Q00B900A23Q0006B700BA00AE000100082Q0046012Q00524Q0046012Q00514Q0046012Q004F4Q0046012Q00A34Q0046012Q007F4Q0046012Q004E4Q0046012Q00804Q0046012Q00B44Q000E00B600BA00014Q00B600873Q00122Q00B7007D3Q00122Q00B800736Q00B900A23Q0006B700BA00AF000100062Q0046012Q00524Q0046012Q00514Q0046012Q004F4Q0046012Q00A34Q0046012Q004E4Q0046012Q00B54Q00EE00B600BA00012Q006200B600B63Q0006B700B600B0000100012Q0046012Q000C3Q0006B700B700B1000100022Q0046012Q000C4Q0046012Q00504Q001301B83Q00010012A100B900B8015Q00BA8Q00B800B900BA00122Q00B9005C012Q00122Q00BA005D015Q00B900B900BA00121600BA005B013Q007300BA008600BA0006B700BB00B2000100012Q0046012Q00B84Q000E00B900BB00014Q00B900873Q00122Q00BA005B3Q00122Q00BB00736Q00BC00A23Q0006B700BD00B30001000F2Q0046012Q00524Q0046012Q00B64Q0046012Q00394Q0046012Q00514Q0046012Q004F4Q0046012Q00B74Q0046012Q007F4Q0046012Q004E4Q0046012Q00B84Q0046012Q00804Q0046012Q00534Q0046012Q00574Q0046012Q00124Q0046012Q00AB4Q0046012Q00A14Q000E00B900BD00014Q00B900873Q00122Q00BA005C3Q00122Q00BB00736Q00BC00A23Q0006B700BD00B4000100072Q0046012Q00B64Q0046012Q007E4Q0046012Q004C4Q0046012Q00574Q0046012Q00124Q0046012Q004E4Q0046012Q00804Q00EE00B900BD00012Q000F00B76Q006200B700B74Q001301B8000C3Q00125201B9005F3Q00122Q00BA00B9012Q00122Q00BB00BA012Q00122Q00BC00BB012Q00122Q00BD00BC012Q00122Q00BE00BD012Q00122Q00BF00BE012Q00122Q00C000BF012Q00122Q00C100C0012Q00122Q00C200C1012Q00121600C300C2012Q00121600C400C3013Q002301B8000C00012Q004601B700B84Q006A00B83Q001100122Q00B900C4012Q00122Q00BA00296Q00B800B900BA00122Q00B900C5012Q00122Q00BA00C56Q00B800B900BA00122Q00B900C6012Q00122Q00BA0026015Q00B800B900BA00121600B900C7012Q00121600BA00C8013Q009E00B800B900BA00121600B900C9012Q00121600BA00674Q009E00B800B900BA00121600B900CA012Q00121600BA00384Q009E00B800B900BA00121600B900CB012Q00121600BA0006013Q009E00B800B900BA00121600B900CC012Q00121600BA00D54Q009E00B800B900BA00121600B900CD012Q00121600BA00CE013Q009E00B800B900BA00121600B900CF012Q00121600BA001D4Q009E00B800B900BA00121600B900D0012Q00121600BA00974Q009E00B800B900BA00121600B9008A012Q00121600BA00314Q009E00B800B900BA00121600B900D1012Q00121600BA00E74Q009E00B800B900BA00121600B900D2012Q00121600BA003E4Q009E00B800B900BA00121600B900D3012Q00121600BA009A4Q009E00B800B900BA00121600B900D4012Q00121600BA00D44Q009E00B800B900BA00121600B900D5012Q00121600BA00984Q009E00B800B900BA00121600B900D6012Q00121600BA0007013Q009E00B800B900BA0006B700B900B5000100012Q0046012Q00A63Q0006B700BA00B6000100012Q0046012Q00543Q0006B700BB00B7000100012Q0046012Q00BA3Q0006B700BC00B8000100042Q0046012Q00AF4Q0046012Q00B84Q0046012Q00A94Q0046012Q00B04Q004601BD00873Q00121600BE00603Q00121600BF00D7012Q0006B700C000B9000100032Q0046012Q00124Q0046012Q00B94Q0046012Q00BB3Q0006B700C100BA000100092Q0046012Q00524Q0046012Q00514Q0046012Q007F4Q0046012Q00124Q0046012Q00BC4Q0046012Q00B04Q0046012Q00A74Q0046012Q004E4Q0046012Q00B93Q0006B700C200BB000100012Q0046012Q00124Q00EE00BD00C200012Q006200BD00BD3Q0006B700BE00BC000100012Q0046012Q00BD4Q004601BF00873Q00121600C0005D3Q00121600C1009F3Q0006B700C200BD000100022Q0046012Q00BB4Q0046012Q00B93Q0006B700C300BE0001000A2Q0046012Q00BB4Q0046012Q00794Q0046012Q007A4Q0046012Q00744Q0046012Q007B4Q0046012Q00754Q0046012Q00124Q0046012Q00BA4Q0046012Q00574Q0046012Q00BE4Q00EE00BF00C300012Q004601BF00873Q00121600C000623Q00121600C100D7012Q0006B700C200BF000100012Q0046012Q00123Q0006B700C300C0000100022Q0046012Q004E4Q0046012Q00394Q00EE00BF00C300012Q000F00B85Q00128801B80028012Q00121600B90029013Q007300B800B800B90006B700B900C1000100052Q0046012Q001D4Q0046012Q00164Q0046012Q00124Q0046012Q000C4Q0046012Q000D4Q007001B8000200014Q00B800213Q00122Q00B900D8015Q00B9000C00B900202Q00B900B900F60006B700BB00C2000100012Q0046012Q00054Q00A101B900BB4Q00F700B83Q000100128801B80028012Q00121600B90029013Q007300B800B800B90006B700B900C3000100062Q0046012Q001D4Q0046012Q00164Q0046012Q00124Q0046012Q00054Q0046012Q000D4Q0046012Q005F4Q003300B8000200012Q006200B800B84Q004601B900213Q00121600BA0057013Q007300BA000300BA00208D00BA00BA00F60006B700BC00C4000100052Q0046012Q00124Q0046012Q00B84Q0046012Q004C4Q0046012Q00194Q0046012Q000C4Q00A101BA00BC4Q00F700B93Q00012Q006200B900B94Q00E700BA5Q00028500BB00C53Q0006B700B900C6000100062Q0046012Q000B4Q0046012Q00BA4Q0046012Q00214Q0046012Q00124Q0046012Q00BB4Q0046012Q000C4Q000F00BA6Q006200BA00BA4Q001301BB5Q0006B700BC00C7000100012Q0046012Q00BB3Q0006B700BD00C8000100052Q0046012Q00BB4Q0046012Q00BC4Q0046012Q00194Q0046012Q00164Q0046012Q00123Q0006B700BE00C9000100022Q0046012Q00064Q0046012Q00533Q0006B700BF00CA0001000C2Q0046012Q004C4Q0046012Q00124Q0046017Q0046012Q000C4Q0046012Q00BD4Q0046012Q00AA4Q0046012Q00B14Q0046012Q00BE4Q0046012Q00544Q0046012Q00534Q0046012Q00BB4Q0046012Q00BC3Q0006B700BA00CB000100022Q0046012Q00BB4Q0046012Q00BC3Q0012C600C000C86Q00C100213Q00122Q00C20057015Q00C2000300C200202Q00C200C200F60006B700C400CC000100052Q0046012Q00C04Q0046012Q00124Q0046012Q00BF4Q0046012Q00BB4Q0046012Q00BA4Q00A101C200C44Q00F700C13Q00012Q000F00BB5Q00121600BB00D9013Q007300BB003E00BB00121600BC00DA013Q007801BB0002000100122Q00BB00DB015Q00BB003E00BB00122Q00BC00DC012Q00122Q00BD00413Q00122Q00BE00DD015Q00BB00BE000100122Q00BB00DB015Q00BB003E00BB00122Q00BC00DE012Q00121600BD00423Q00121600BE00DD013Q00EE00BB00BE000100121600BB00D9013Q007300BB003E00BB00121600BC00DF013Q007801BB0002000100122Q00BB00DB015Q00BB003E00BB00122Q00BC00E0012Q00122Q00BD00433Q00122Q00BE00DD015Q00BB00BE000100122Q00BB00D9015Q00BB003E00BB00122Q00BC00E1013Q007801BB0002000100122Q00BB00DB015Q00BB003E00BB00122Q00BC00E2012Q00122Q00BD00443Q00122Q00BE00DD015Q00BB00BE000100122Q00BB00E3015Q00BB003E00BB00122Q00BC00E4012Q00125800BD00E5012Q00122Q00BE00466Q00BB00BE000100122Q00BB00DB015Q00BB003E00BB00122Q00BC00E6012Q00122Q00BD00453Q00122Q00BE00DD015Q00BB00BE000100122Q00BB00D9013Q007300BB003E00BB00121600BC00E7013Q003300BB0002000100121600BB00E8013Q007300BB003E00BB00122600BC00E9012Q00122Q00BD00EA012Q00122Q00BE00BC3Q00122Q00BF00193Q00122Q00C000186Q00BB00C0000100122Q00BB00E3015Q00BB003E00BB00122Q00BC00EB012Q00122Q00BD00EC012Q0012A200BE00226Q00BB00BE000100122Q00BB00E3015Q00BB003E00BB00122Q00BC00ED012Q00122Q00BD00EE012Q00122Q00BE00326Q00BB00BE000100122Q00BB00E3015Q00BB003E00BB00121600BC00EF012Q00121600BD00F0012Q00121600BE00274Q00EE00BB00BE000100121600BB00F1013Q007300BB003F00BB00121600BC00F2013Q003300BB0002000100121600BB00D9013Q007300BB003F00BB00121600BC00F3013Q007801BB0002000100122Q00BB00DB015Q00BB003F00BB00122Q00BC00F4012Q00122Q00BD00473Q00122Q00BE00DD015Q00BB00BE000100122Q00BB00D9015Q00BB003F00BB00122Q00BC00F5013Q003300BB0002000100126B00BB00DB015Q00BB003F00BB00122Q00BC00F6012Q00122Q00BD00486Q00BB00BD000100122Q00BB00DB015Q00BB003F00BB00122Q00BC00F7012Q00122Q00BD00496Q00BB00BD000100121600BB00DB013Q007300BB003F00BB00121600BC00F8012Q00121600BD004A4Q00EE00BB00BD000100121600BB00D9013Q007300BB003F00BB00123900BC00F9015Q00BB0002000100122Q00BB00DB015Q00BB003F00BB00122Q00BC00FA012Q00122Q00BD004B6Q00BB00BD000100122Q00BB00DB015Q00BB003F00BB00122Q00BC00FB012Q00121600BD004C4Q00EE00BB00BD000100121600BB00D9013Q007300BB003F00BB00123900BC00FC015Q00BB0002000100122Q00BB00DB015Q00BB003F00BB00122Q00BC00FD012Q00122Q00BD004D6Q00BB00BD000100122Q00BB00DB015Q00BB003F00BB00122Q00BC00FE012Q0012A200BD004E6Q00BB00BD000100122Q00BB00DB015Q00BB003F00BB00122Q00BC00FF012Q00122Q00BD004F3Q00122Q00BE00DD015Q00BB00BE000100122Q00BB00E8015Q00BB003F00BB00122600BC2Q00022Q00122Q00BD0001022Q00122Q00BE00C8012Q00122Q00BF009F3Q00122Q00C0003D6Q00BB00C0000100122Q00BB00E3015Q00BB003F00BB00122Q00BC002Q022Q00122Q00BD0003022Q00121600BE003F4Q00EE00BB00BE000100121600BB00D9013Q007300BB004000BB00121600BC0004023Q007801BB0002000100122Q00BB00DB015Q00BB004000BB00122Q00BC0005022Q00122Q00BD007B3Q00122Q00BE00DD015Q00BB00BE000100122Q00BB0006025Q00BB004000BB00122Q00BC0007022Q00121600BD0008022Q00121600BE0009022Q0006B700BF00CD000100032Q0046012Q00124Q0046012Q00B34Q0046012Q00144Q001601BB00BF000100122Q00BB00DB015Q00BB004000BB00122Q00BC000A022Q00122Q00BD007C3Q00122Q00BE00DD013Q00EE00BB00BE000100121600BB00D9013Q007300BB004000BB00121600BC000B023Q007801BB0002000100122Q00BB00DB015Q00BB004000BB00122Q00BC000C022Q00122Q00BD00593Q00122Q00BE00DD015Q00BB00BE000100122Q00BB00DB015Q00BB004000BB00122Q00BC000D022Q00121600BD007D3Q00121600BE00DD013Q00EE00BB00BE000100121600BB00D9013Q007300BB004000BB00121600BC000E023Q007801BB0002000100122Q00BB00DB015Q00BB004000BB00122Q00BC000F022Q00122Q00BD005A3Q00122Q00BE00DD015Q00BB00BE000100122Q00BB00F1015Q00BB004000BB00122Q00BC0010023Q003300BB0002000100121600BB00F1013Q007300BB004100BB00121600BC0011023Q009C01BB0002000200121600BC00D9013Q007300BC004100BC00121600BD0012023Q007801BC0002000100122Q00BC00DB015Q00BC004100BC00122Q00BD0013022Q00122Q00BE005B3Q00122Q00BF00DD015Q00BC00BF000100122Q00BC00DB015Q00BC004100BC00122Q00BD0014022Q00121600BE005C3Q00121600BF00DD013Q00EE00BC00BF000100121600BC00F1013Q007300BC004100BC00121600BD0015023Q003300BC0002000100128801BC0028012Q00121600BD0029013Q007300BC00BC00BD0006B700BD00CE000100042Q0046012Q001D4Q0046012Q00164Q0046012Q00B64Q0046012Q00BB4Q003300BC0002000100121600BC00D9013Q007300BC004200BC00121600BD0016023Q003300BC0002000100121600BC0017023Q007300BC004200BC00121600BD0018022Q00121600BE0019023Q004601BF00B73Q00127E01C0005E6Q00BC00C0000100122Q00BC00DB015Q00BC004200BC00122Q00BD001A022Q00122Q00BE00606Q00BC00BE000100122Q00BC00E3015Q00BC004200BC00122Q00BD001B022Q00121600BE001C022Q00121600BF00614Q00EE00BC00BF000100121600BC00D9013Q007300BC004200BC00123900BD001D025Q00BC0002000100122Q00BC00DB015Q00BC004200BC00122Q00BD001E022Q00122Q00BE005D6Q00BC00BE000100122Q00BC00DB015Q00BC004200BC00122Q00BD001F022Q00121600BE00624Q00EE00BC00BE000100121600BC00F1013Q007300BC004200BC00121600BD0020023Q003300BC0002000100121600BC00D9013Q007300BC004100BC00121600BD0021023Q007801BC0002000100122Q00BC00E3015Q00BC004100BC00122Q00BD0022022Q00122Q00BE0023022Q00122Q00BF00636Q00BC00BF000100122Q00BC00E3015Q00BC004100BC00122Q00BD0024022Q00121600BE0025022Q00121600BF00644Q00EE00BC00BF000100121600BC00F1013Q007300BC004100BC00121600BD0026023Q003300BC0002000100121600BC00F1013Q007300BC004300BC00121600BD0027023Q003300BC0002000100121600BC00F1013Q007300BC004300BC00121600BD0028023Q009C01BC0002000200121600BD006E012Q0006B700BE00CF000100012Q0046012Q00BC4Q008B013700BD00BE00122Q00BD00D9015Q00BD004300BD00122Q00BE0029025Q00BD0002000100122Q00BD0020015Q00BE00A86Q00BD000200BF00044Q00110B0100121600C200E3013Q007300C2004300C200121600C30090013Q007300C300C100C300121600C4002A022Q00121600C5008F013Q007300C500C100C52Q00EE00C200C5000100062B00BD00090B01000200040F012Q00090B0100121600BD00D9013Q007300BD004300BD00121600BE002B023Q003300BD0002000100121600BD00E8013Q007300BD004300BD00122600BE002C022Q00122Q00BF002D022Q00122Q00C0001D3Q00122Q00C1002E022Q00122Q00C200396Q00BD00C2000100122Q00BD00E8015Q00BD004300BD00122Q00BE002F022Q00122Q00BF0030022Q00121600C000BC3Q00125800C100193Q00122Q00C2003B6Q00BD00C2000100122Q00BD00E3015Q00BD004300BD00122Q00BE0031022Q00122Q00BF0032022Q00122Q00C0003C6Q00BD00C0000100122Q00BD00E3013Q007300BD004300BD00121600BE0033022Q00121600BF0034022Q00121600C000404Q00EE00BD00C0000100121600BD00D9013Q007300BD004400BD00123900BE0035025Q00BD0002000100122Q00BD00DB015Q00BD004400BD00122Q00BE0035022Q00122Q00BF00576Q00BD00BF000100122Q00BD00E3015Q00BD004400BD00122Q00BE0036022Q00125800BF0037022Q00122Q00C000586Q00BD00C0000100122Q00BD00E3015Q00BD004400BD00122Q00BE0038022Q00122Q00BF0039022Q00122Q00C000366Q00BD00C0000100122Q00BD00E8013Q007300BD004400BD00122600BE003A022Q00122Q00BF003B022Q00122Q00C00026012Q00122Q00C10004012Q00122Q00C200376Q00BD00C2000100122Q00BD00E8015Q00BD004400BD00122Q00BE003C022Q00122Q00BF0030022Q00121600C000BC3Q00121600C100193Q00121600C200344Q00EE00BD00C2000100121600BD00F1013Q007300BD004400BD00121600BE003D023Q009C01BD000200022Q004601AC00BD3Q00121600BD0006023Q007300BD004400BD00121600BE003E022Q00121600BF003F022Q00121600C00040022Q0006B700C100D0000100022Q0046012Q00854Q0046012Q00384Q001601BD00C1000100122Q00BD0006025Q00BD004400BD00122Q00BE0041022Q00122Q00BF0042022Q00122Q00C00043022Q0006B700C100D1000100022Q0046012Q00AD4Q0046012Q00AE4Q00EE00BD00C1000100121600BD00F1013Q007300BD004500BD00121600BE0044023Q009C01BD000200022Q006200BE00BE3Q0006B700BF00D2000100052Q0046012Q00524Q0046012Q00544Q0046012Q00BE4Q0046012Q00BD4Q0046012Q00513Q00121600C000D9013Q007300C0004500C000121600C10045023Q007801C00002000100122Q00C000E3015Q00C0004500C000122Q00C10046022Q00122Q00C20047022Q00122Q00C3006E6Q00C000C3000100122Q00C00017025Q00C0004500C000122Q00C10048022Q00121600C20049023Q001301C35Q00121600C400774Q006200C500C53Q00121600C600384Q00FC00C000C600022Q004601BE00C04Q004601C000BF4Q006101C00001000100121600C000C83Q00121600C100E3013Q007300C1004500C100121600C2004A022Q00121600C3004B022Q00121600C4004C022Q0006B700C500D30001000A2Q0046012Q00C04Q0046012Q001F4Q0046012Q001D4Q0046012Q00124Q0046012Q00BD4Q0046012Q00914Q0046012Q009D4Q0046012Q00544Q0046012Q00574Q0046012Q00394Q001601C100C5000100122Q00C100E8015Q00C1004500C100122Q00C2004D022Q00122Q00C30030022Q00122Q00C400733Q00121600C500193Q00121600C600354Q001601C100C6000100122Q00C10006025Q00C1004500C100122Q00C2004E022Q00122Q00C3004F022Q00122Q00C40043023Q004601C500BF4Q00EE00C100C5000100121600C100D9013Q007300C1004500C100121600C20050023Q003300C1000200010006B700C100D4000100022Q0046012Q00BD4Q0046012Q004E3Q00121600C20006023Q007300C2004500C200121600C30004022Q00121600C40051022Q00121600C50052022Q0006B700C600D5000100012Q0046012Q00C14Q001601C200C6000100122Q00C20006025Q00C2004500C200122Q00C3000B022Q00122Q00C40053022Q00122Q00C50052022Q0006B700C600D6000100012Q0046012Q00C14Q001601C200C6000100122Q00C20006025Q00C2004500C200122Q00C3000E022Q00122Q00C40054022Q00122Q00C50052022Q0006B700C600D7000100012Q0046012Q00C14Q001601C200C6000100122Q00C200E3015Q00C2004600C200122Q00C30055022Q00122Q00C40056022Q00122Q00C5006A4Q001601C200C5000100122Q00C200E3015Q00C2004600C200122Q00C30057022Q00122Q00C40058022Q00122Q00C5006B4Q001601C200C5000100122Q00C200E3015Q00C2004600C200122Q00C30059022Q00122Q00C4005A022Q00122Q00C5006C4Q001601C200C5000100122Q00C200E3015Q00C2004600C200122Q00C3005B022Q00122Q00C4005C022Q00122Q00C5006D4Q001601C200C5000100122Q00C200E3015Q00C2004600C200122Q00C3005D022Q00122Q00C4005E022Q00122Q00C5006F4Q001601C200C5000100122Q00C200E3015Q00C2004600C200122Q00C3005F022Q00122Q00C40060022Q00122Q00C500703Q0006B700C600D8000100012Q0046012Q00BA4Q001601C200C6000100122Q00C200E3015Q00C2004700C200122Q00C30061022Q00122Q00C40062022Q00122Q00C500713Q0006B700C600D9000100012Q0046012Q004B4Q001601C200C6000100122Q00C200E8015Q00C2004700C200122Q00C30063022Q00122Q00C40064022Q00122Q00C500D43Q00125800C600193Q00122Q00C700726Q00C200C7000100122Q00C200E3015Q00C2004700C200122Q00C30065022Q00122Q00C40066022Q00122Q00C500746Q00C200C5000100122Q00C200E3013Q00A801C2004700C200122Q00C30067022Q00122Q00C40068022Q00122Q00C500756Q00C200C5000100122Q00C200E3015Q00C2004700C200122Q00C30069022Q00122Q00C4006A022Q00122Q00C500764Q00EE00C200C500012Q004601C200213Q00121600C30057013Q007300C3000300C300208D00C300C300F60006B700C500DA000100032Q0046012Q00124Q0046012Q004B4Q0046012Q004C4Q003100C300C56Q00C23Q00014Q00C200213Q00122Q00C3006B025Q00C3000200C300202Q00C300C300F60006B700C500DB000100022Q0046012Q00124Q0046012Q004B4Q00A101C300C54Q00F700C23Q000100121600C200D9013Q007300C2004800C200121600C3006C023Q007801C20002000100122Q00C200E3015Q00C2004800C200122Q00C3006C022Q00122Q00C4006D022Q00122Q00C500656Q00C200C5000100122Q00C200E8015Q00C2004800C200122Q00C3006E022Q00121600C4006F022Q00121600C500293Q00121600C6001D3Q00121600C700664Q00EE00C200C7000100121600C200F1013Q007300C2004800C200121600C30070023Q003300C20002000100121600C200D9013Q007300C2004700C200121600C30071023Q003300C20002000100121600C20072023Q007300C2004700C200121600C30073022Q00121600C40074023Q001301C500054Q00AE00C63Q000200122Q00C70090012Q00122Q00C80075025Q00C600C700C800122Q00C7008F012Q00202Q00C600C700824Q00C73Q000200122Q00C80090012Q00122Q00C90076025Q00C700C800C900121600C8008F012Q00202E00C700C800834Q00C83Q000200122Q00C90090012Q00122Q00CA0077025Q00C800C900CA00122Q00C9008F012Q00202Q00C800C900844Q00C93Q000200122Q00CA0090012Q00122Q00CB0078023Q009E00C900CA00CB00121600CA008F012Q00202C00C900CA00852Q001301CA3Q000200121600CB0090012Q00121600CC0079023Q009E00CA00CB00CC00121600CB008F012Q00202C00CA00CB00862Q002301C5000500012Q00EE00C200C5000100121600C200E8013Q007300C2004700C200122600C3007A022Q00122Q00C4007B022Q00122Q00C500293Q00122Q00C600733Q00122Q00C7007F6Q00C200C7000100122Q00C20017025Q00C2004700C200122Q00C3007C022Q00122Q00C4007D023Q001301C500063Q00121600C600813Q00121600C700213Q00121C00C8007E022Q00122Q00C90077022Q00122Q00CA0078022Q00122Q00CB007F025Q00C50006000100121600C600804Q001C01C200C6000100122Q00C200F1015Q00C2004700C200122Q00C30080025Q00C20002000200122Q00C300E3015Q00C3004700C300122Q00C40071022Q00122Q00C50081022Q00122Q00C6007E3Q0006B700C700DC000100012Q0046012Q00C24Q00EE00C300C7000100128801C30028012Q00121600C40029013Q007300C300C300C40006B700C400DD000100062Q0046012Q000C4Q0046012Q001D4Q0046012Q00164Q0046012Q00124Q0046012Q00C24Q0046012Q004E4Q003300C30002000100121600C300D9013Q007300C3004800C300121600C40082023Q003300C30002000100121600C300E3013Q007300C3004800C300121600C40083022Q00121600C50084022Q00121600C600683Q0006B700C700DE000100012Q0046012Q00B94Q001601C300C7000100122Q00C300E3015Q00C3004800C300122Q00C40085022Q00122Q00C50086022Q00122Q00C600694Q001601C300C6000100122Q00C30006025Q00C3004800C300122Q00C40087022Q00122Q00C50088022Q00122Q00C60089023Q004601C700B94Q00EE00C300C700012Q001301C3001B3Q00125201C4008A022Q00122Q00C5008B022Q00122Q00C6008C022Q00122Q00C7008D022Q00122Q00C8008E022Q00122Q00C9008F022Q00122Q00CA0090022Q00122Q00CB0091022Q00122Q00CC0092022Q00122Q00CD0093022Q00125201CE0094022Q00122Q00CF0095022Q00122Q00D00096022Q00122Q00D10097022Q00122Q00D20098022Q00122Q00D30099022Q00122Q00D4009A022Q00122Q00D5009B022Q00122Q00D6009C022Q00122Q00D7009D022Q00125201D8009E022Q00122Q00D9009F022Q00122Q00DA00A0022Q00122Q00DB00A1022Q00122Q00DC00A2022Q00122Q00DD00A3022Q00122Q00DE00A4022Q00122Q00DF00A5022Q00122Q00E000A6022Q00122Q00E100A7022Q00125201E200A8022Q00122Q00E300A9022Q00122Q00E400AA022Q00122Q00E500AB022Q00122Q00E600AC022Q00122Q00E700AD022Q00122Q00E800AE022Q00122Q00E900AF022Q00122Q00EA00B0022Q00122Q00EB00B1022Q00121600EC00B2023Q002301C3002900012Q00E700C46Q006200C500C53Q00121600C60006023Q007300C6004800C600121600C700B3022Q00121600C800B4022Q00121600C900B5022Q0006B700CA00DF000100052Q0046012Q00C44Q0046012Q00044Q0046012Q00C54Q0046012Q00C34Q0046012Q001D4Q00A500C600CA00024Q00C500C63Q00122Q00C600D9015Q00C6003D00C600122Q00C700B6025Q00C60002000100122Q00C600E8015Q00C6003D00C600122Q00C700B7022Q00122Q00C800B8022Q00121600C900293Q00121600CA00313Q00121600CB00284Q00EE00C600CB000100121600C60017023Q007300C6003D00C600121600C700B9022Q00121600C800BA023Q001301C900073Q00121600CA002B3Q00121600CB004A012Q00121600CC00BB022Q00121C00CD004F012Q00122Q00CE0050012Q00122Q00CF004D012Q00122Q00D0004E015Q00C90007000100121600CA002A4Q001601C600CA000100122Q00C600E8015Q00C6003D00C600122Q00C700BC022Q00122Q00C800BD022Q00122Q00C900BE022Q00121600CA00BF022Q00121600CB002C4Q001601C600CB000100122Q00C600E8015Q00C6003D00C600122Q00C700C0022Q00122Q00C800C1022Q00122Q00C900BC3Q00121600CA00C2022Q00121600CB002E4Q001601C600CB000100122Q00C600E8015Q00C6003D00C600122Q00C700C3022Q00122Q00C800C4022Q00122Q00C900293Q00121600CA00BC3Q00121600CB00304Q00EE00C600CB000100121600C600D9013Q007300C6003D00C600121600C700C5023Q003300C60002000100121600C60017023Q007300C6003D00C600121600C700C6022Q00121600C800C7023Q001301C900043Q00121C00CA00213Q00122Q00CB0077022Q00122Q00CC0078022Q00122Q00CD00C8025Q00C90004000100121600CA00204Q007B01C600CA000100122Q00C60017025Q00C6003D00C600122Q00C700C9022Q00122Q00C800CA025Q00C900023Q00122Q00CA001B3Q00122Q00CB00CB025Q00C90002000100121600CA001A4Q001601C600CA000100122Q00C600E8015Q00C6003D00C600122Q00C700CC022Q00122Q00C80030022Q00122Q00C900BC3Q00121600CA00193Q00121600CB00334Q001601C600CB000100122Q00C600E8015Q00C6003D00C600122Q00C700CD022Q00122Q00C800CE022Q00122Q00C90026012Q00121600CA0004012Q00121600CB001C4Q00EE00C600CB000100121600C60017023Q007300C6003D00C600121600C700CF022Q00121600C800D0023Q001301C900033Q00121600CA001F3Q00121600CB00D1022Q00121600CC00D2023Q002301C90003000100121600CA001E4Q001601C600CA000100122Q00C600E3015Q00C6003D00C600122Q00C700D3022Q00122Q00C800D4022Q00122Q00C900244Q00EE00C600C9000100121600C600D9013Q007300C6003D00C600121600C700D5023Q007801C60002000100122Q00C600E3015Q00C6003D00C600122Q00C700D6022Q00122Q00C800D7022Q00122Q00C900266Q00C600C9000100122Q00C60006025Q00C6003D00C600122Q00C700D8022Q00121600C800D9022Q00121600C900DA023Q004601CA00304Q001601C600CA000100122Q00C60006025Q00C6003D00C600122Q00C700DB022Q00122Q00C800DC022Q00122Q00C900DB023Q004601CA00224Q00EE00C600CA000100121600C600D9013Q007300C6003D00C600121600C700DD023Q003300C60002000100121600C600F1013Q007300C6003D00C600121600C700DE023Q009C01C6000200022Q0046014A00C63Q00121600C600F1013Q007300C6003D00C600121600C700DF023Q003300C60002000100121600C600E0022Q00128801C700133Q0006B700C800E0000100012Q0046012Q00C64Q003300C70002000100128801C70028012Q00121600C80029013Q007300C700C700C80006B700C800E1000100082Q0046012Q001D4Q0046012Q00164Q0046012Q00524Q0046012Q002A4Q0046012Q000F4Q0046012Q00514Q0046012Q004F4Q0046012Q00C64Q003300C7000200010020E300C70012006800069A01C700940D013Q00040F012Q00940D012Q004601C700B94Q006101C7000100012Q004601C700354Q004601C8003E4Q003300C7000200012Q004601C7008A4Q006101C70001000100128801C700E1022Q00121600C800E2023Q004601C9000E3Q00121600CA00E3023Q008700C800C800CA2Q003300C70002000100128801C700133Q0006B700C800E2000100022Q0046012Q00094Q0046012Q000E4Q003300C7000200012Q000B012Q00013Q00E33Q00033Q0003043Q0067616D65030A3Q004765745365727669636503133Q005669727475616C496E7075744D616E6167657200063Q001288012Q00013Q00208D5Q0002001216000200034Q00FC3Q000200022Q00B88Q000B012Q00017Q00063Q0003063Q00697366696C65030A3Q004A534F4E4465636F646503083Q007265616466696C6503053Q0070616972730003043Q007479706500243Q001288012Q00013Q00069A012Q002300013Q00040F012Q00230001001288012Q00014Q004D00016Q009C012Q0002000200069A012Q002300013Q00040F012Q002300012Q004D3Q00013Q00201F014Q000200122Q000200036Q00038Q000200039Q00000200122Q000100046Q00028Q00010002000300044Q002100012Q004D000600024Q007300060006000400267B000600210001000500040F012Q00210001001288010600064Q0026010700056Q00060002000200122Q000700066Q000800026Q0008000800044Q00070002000200062Q000600210001000700040F012Q002100012Q004D000600024Q009E00060004000500062B000100120001000200040F012Q001200012Q000B012Q00017Q00033Q0003043Q007461736B03053Q0064656C6179026Q33E33F00104Q004D7Q00069A012Q000400013Q00040F012Q000400012Q000B012Q00014Q00E73Q00014Q00B87Q001288012Q00013Q0020E35Q0002001216000100033Q0006B700023Q000100042Q004D8Q004D3Q00014Q004D3Q00024Q004D3Q00034Q00EE3Q000200012Q000B012Q00013Q00013Q00013Q0003053Q007063612Q6C00094Q00E78Q00B87Q001288012Q00013Q0006B700013Q000100032Q004D3Q00014Q004D3Q00024Q004D3Q00034Q00333Q000200012Q000B012Q00013Q00013Q00023Q0003093Q00777269746566696C65030A3Q004A534F4E456E636F6465000B3Q001288012Q00013Q00069A012Q000A00013Q00040F012Q000A0001001288012Q00014Q004D00016Q004D000200013Q00208D0002000200022Q004D000400024Q00A1010200044Q00F75Q00012Q000B012Q00017Q00023Q0003073Q0067657467656E76030C3Q004F52494F4E5F554E4C4F4144000D3Q001288012Q00013Q00069A012Q000C00013Q00040F012Q000C0001001288012Q00014Q0065012Q000100020020E35Q000200069A012Q000C00013Q00040F012Q000C0001001288012Q00014Q0065012Q000100020020E35Q00022Q0061012Q000100012Q000B012Q00017Q00013Q0003053Q007063612Q6C01053Q0012882Q0100013Q0006B700023Q000100012Q0046017Q00330001000200012Q000B012Q00013Q00013Q00063Q0003063Q0069706169727303053Q004F52494F4E03073Q004245544148554203043Q0059554258030E3Q0046696E6446697273744368696C6403073Q0044657374726F7900133Q0012073Q00016Q000100033Q00122Q000200023Q00122Q000300033Q00122Q000400046Q0001000300012Q00B23Q0002000200040F012Q001000012Q004D00055Q00208D0005000500052Q0046010700044Q00FC00050007000200069A0105001000013Q00040F012Q0010000100208D0006000500062Q003300060002000100062B3Q00080001000200040F012Q000800012Q000B012Q00017Q00033Q0003043Q0067616D65030A3Q004765745365727669636503073Q00436F726547756900074Q0073016Q00122Q000100013Q00202Q00010001000200122Q000300036Q000100039Q0000016Q00017Q00023Q00030C3Q0057616974466F724368696C6403093Q00506C6179657247756900074Q004D8Q004D000100013Q00208D000100010001001216000300024Q00A12Q0100034Q00F75Q00012Q000B012Q00017Q00013Q0003063Q0067657468756900083Q001288012Q00013Q00069A012Q000700013Q00040F012Q000700012Q004D7Q0012882Q0100014Q00772Q0100014Q00F75Q00012Q000B012Q00017Q00053Q0003063Q00506172656E7403063Q0067657468756903043Q0067616D65030A3Q004765745365727669636503073Q00436F7265477569000E4Q004D7Q0012882Q0100023Q00069A2Q01000800013Q00040F012Q000800010012882Q0100024Q00652Q01000100020006572Q01000C0001000100040F012Q000C00010012882Q0100033Q00208D000100010004001216000300054Q00FC00010003000200105D012Q000100012Q000B012Q00017Q00043Q0003083Q00496E7374616E63652Q033Q006E657703053Q00706169727303063Q00506172656E74030E3Q0012A9010300013Q00202Q0003000300024Q00048Q00030002000200122Q000400036Q000500016Q00040002000600044Q000900012Q009E00030007000800062B000400080001000200040F012Q0008000100105D0103000400022Q00DA000300024Q000B012Q00017Q00063Q0003083Q005549436F726E6572030C3Q00436F726E657252616469757303043Q005544696D2Q033Q006E6577028Q00026Q002040020E4Q004D00025Q001216000300014Q001301043Q0001001288010500033Q0020E3000500050004001216000600053Q00068E000700090001000100040F012Q00090001001216000700064Q00FC00050007000200105D0104000200052Q004601056Q00EE0002000500012Q000B012Q00017Q00043Q00030D3Q0055736572496E7075745479706503043Q00456E756D030C3Q004D6F75736542752Q746F6E3103053Q00546F75636801103Q00202D2Q013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000D0001000200040F012Q000D00010020E300013Q0001001288010200023Q0020E30002000200010020E30002000200040006AD0001000D0001000200040F012Q000D00012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00043Q00030D3Q0055736572496E7075745479706503043Q00456E756D030D3Q004D6F7573654D6F76656D656E7403053Q00546F75636801103Q00202D2Q013Q000100122Q000200023Q00202Q00020002000100202Q00020002000300062Q0001000D0001000200040F012Q000D00010020E300013Q0001001288010200023Q0020E30002000200010020E30002000200040006AD0001000D0001000200040F012Q000D00012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00023Q0003053Q007461626C6503063Q00696E7365727401073Q0012882Q0100013Q0020E30001000100022Q004D00026Q004601036Q00EE0001000300012Q00DA3Q00024Q000B012Q00017Q00023Q0003063Q0069706169727303053Q007063612Q6C00164Q004A012Q00019Q003Q00124Q00016Q000100018Q0002000200044Q000B0001001288010500023Q0006B700063Q000100012Q0046012Q00044Q00330005000200012Q000F00035Q00062B3Q00060001000200040F012Q00060001001288012Q00023Q0006B700010001000100012Q004D3Q00024Q00333Q00020001001288012Q00023Q0006B700010002000100012Q004D3Q00034Q00333Q000200012Q000B012Q00013Q00033Q00013Q00030A3Q00446973636F2Q6E65637400044Q004D7Q00208D5Q00012Q00333Q000200012Q000B012Q00017Q00023Q0003143Q00556E62696E6446726F6D52656E6465725374657003083Q004F52494F4E41696D00054Q0075016Q00206Q000100122Q000200028Q000200016Q00017Q00013Q0003073Q0044657374726F7900044Q004D7Q00208D5Q00012Q00333Q000200012Q000B012Q00017Q00023Q0003073Q0067657467656E76030C3Q004F52494F4E5F554E4C4F414400083Q001288012Q00013Q00069A012Q000700013Q00040F012Q00070001001288012Q00014Q0065012Q000100022Q004D00015Q00105D012Q000200012Q000B012Q00017Q00173Q00030A3Q005465787442752Q746F6E03043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q003C4003083Q00506F736974696F6E2Q033Q006E6577026Q00F03F028Q00026Q002A4003103Q004261636B67726F756E64436F6C6F723303043Q006361726403043Q0054657874030A3Q0054657874436F6C6F72332Q033Q0074787403043Q00466F6E7403043Q00456E756D030C3Q00476F7468616D4D656469756D03083Q005465787453697A65026Q002840030F3Q004175746F42752Q746F6E436F6C6F720100026Q00204003284Q006A01035Q00122Q000400016Q00053Q000800122Q000600033Q00202Q00060006000400062Q000700080001000200040F012Q00080001001216000700053Q001216000800054Q00FC00060008000200105D010500020006001288010600033Q0020E3000600060007001216000700084Q0046010800013Q001216000900093Q001216000A000A4Q00FC0006000A000200105D0105000600062Q004D000600013Q00202501060006000C00102Q0005000B000600102Q0005000D6Q000600013Q00202Q00060006000F00102Q0005000E000600122Q000600113Q00202Q00060006001000202Q00060006001200102Q0005001000060030930005001300140030930005001500162Q004D000600024Q00FC0003000600022Q004D000400034Q0046010500033Q001216000600174Q00EE0004000600012Q00DA000300024Q000B012Q00017Q00013Q0003073Q0056697369626C6500064Q004D8Q004D00015Q0020E30001000100012Q00A7000100013Q00105D012Q000100012Q000B012Q00017Q00033Q0003073Q004B6579436F646503043Q00456E756D030A3Q0052696768745368696674020B3Q0006572Q01000A0001000100040F012Q000A00010020E300023Q0001001288010300023Q0020E30003000300010020E30003000300030006270002000A0001000300040F012Q000A00012Q004D00026Q00610102000100012Q000B012Q00017Q00013Q0003083Q00506F736974696F6E010D4Q004D00016Q004601026Q009C2Q010002000200069A2Q01000C00013Q00040F012Q000C00012Q00E7000100014Q0002000100013Q00202Q00013Q00014Q000100026Q000100043Q00202Q0001000100014Q000100034Q000B012Q00017Q00073Q0003083Q00506F736974696F6E03053Q005544696D322Q033Q006E657703013Q005803053Q005363616C6503063Q004F2Q6673657403013Q005901214Q004D00015Q00069A2Q01002000013Q00040F012Q002000012Q004D000100014Q004601026Q009C2Q010002000200069A2Q01002000013Q00040F012Q002000010020E300013Q00012Q00A0000200026Q0001000100024Q000200033Q00122Q000300023Q00202Q0003000300034Q000400043Q00202Q00040004000400202Q0004000400054Q000500043Q00202Q00050005000400202Q00050005000600202Q0006000100044Q0005000500064Q000600043Q00202Q00060006000700202Q0006000600054Q000700043Q00202Q00070007000700202Q00070007000600202Q0008000100074Q0007000700084Q00030007000200102Q0002000100032Q000B012Q00019Q002Q0001084Q004D00016Q004601026Q009C2Q010002000200069A2Q01000700013Q00040F012Q000700012Q00E700016Q00B8000100014Q000B012Q00017Q00023Q00026Q00F03F027Q0040010C4Q004D00016Q0073000100013Q0020E30001000100012Q004D000200014Q00600001000100022Q004D00026Q0073000200023Q0020E30002000200022Q004D000300014Q00600002000200032Q0036000100034Q000B012Q00017Q001C3Q0003043Q006D61746803043Q0073717274027Q00402Q033Q0064656703053Q006174616E3203053Q004672616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q00F03F030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577026Q00E03F03083Q00506F736974696F6E03083Q00526F746174696F6E03103Q004261636B67726F756E64436F6C6F723303063Q00436F6C6F723303073Q0066726F6D524742025Q00406540025Q00206740025Q00E06F4003163Q004261636B67726F756E645472616E73706172656E637902CD5QCCDC3F030F3Q00426F7264657253697A65506978656C028Q0003063Q005A496E646578025Q00804940023B4Q004D00026Q004601036Q00B20002000200032Q004D00046Q0046010500014Q00B2000400020005001288010600013Q0020E30006000600022Q003201070004000200203B0107000700032Q003201080005000300203B0108000800032Q00330107000700082Q009C010600020002001288010700013Q0020E3000700070004001288010800013Q0020E30008000800052Q00320109000500032Q0032010A000400022Q00A10108000A4Q000400073Q00022Q004D000800013Q001216000900064Q0013010A3Q0008001288010B00083Q0020E3000B000B00092Q0046010C00063Q001216000D000A4Q00FC000B000D000200105D010A0007000B001288010B000C3Q0020E3000B000B000D001216000C000E3Q001216000D000E4Q00FC000B000D000200105D010A000B000B001288010B00083Q0020E3000B000B00092Q0033010C000200040020EA000C000C00032Q0033010D000300050020EA000D000D00032Q00FC000B000D000200105D010A000F000B00101A010A0010000700122Q000B00123Q00202Q000B000B001300122Q000C00143Q00122Q000D00153Q00122Q000E00166Q000B000E000200102Q000A0011000B00302Q000A0017001800302Q000A0019001A003093000A001B001C2Q004D000B00024Q00EE0008000B00012Q000B012Q00017Q00133Q0003053Q004672616D6503043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574030B3Q00416E63686F72506F696E7403073Q00566563746F72322Q033Q006E6577026Q00E03F03083Q00506F736974696F6E03103Q004261636B67726F756E64436F6C6F7233030F3Q00426F7264657253697A65506978656C028Q0003063Q005A496E646578025Q00804A4002CD5QCC044003163Q004261636B67726F756E645472616E73706172656E6379029A5Q99E93F026Q004A40026Q00084003414Q002F01038Q00048Q0003000200044Q000500013Q00122Q000600016Q00073Q000600122Q000800033Q00202Q0008000800044Q000900016Q000A00016Q0008000A000200102Q00070002000800122Q000800063Q00202Q00080008000700122Q000900083Q00122Q000A00086Q0008000A000200102Q00070005000800122Q000800033Q00202Q0008000800044Q000900036Q000A00046Q0008000A000200102Q00070009000800102Q0007000A000200302Q0007000B000C00302Q0007000D000E4Q000800026Q0005000800024Q000600036Q000700056Q000800016Q0006000800014Q000600013Q00122Q000700016Q00083Q000700122Q000900033Q00202Q00090009000400202Q000A0001000F00202Q000B0001000F4Q0009000B000200102Q00080002000900122Q000900063Q00202Q00090009000700122Q000A00083Q00122Q000B00086Q0009000B000200102Q00080005000900122Q000900033Q00202Q0009000900044Q000A00036Q000B00046Q0009000B000200102Q00080009000900102Q0008000A000200302Q00080010001100302Q0008000B000C00302Q0008000D00124Q000900026Q0006000900024Q000700036Q000800063Q00202Q0009000100134Q0007000900016Q00017Q00153Q0003063Q00737472696E672Q033Q00737562026Q00F03F026Q00104003043Q00682Q747003053Q007063612Q6C030A3Q00496D6167654C6162656C03043Q0053697A6503053Q005544696D322Q033Q006E6577028Q0003163Q004261636B67726F756E645472616E73706172656E637903053Q00496D61676503093Q005363616C655479706503043Q00456E756D03043Q0043726F7003063Q005A496E646578026Q004E40026Q003B4003073Q0056697369626C65012Q002F4Q006E7Q00122Q000100013Q00202Q0001000100024Q00025Q00122Q000300033Q00122Q000400046Q00010004000200262Q000100120001000500040F012Q001200010012882Q0100063Q0006B700023Q000100012Q0046017Q00B200010002000200069A2Q01001100013Q00040F012Q0011000100068E3Q00120001000200040F012Q001200012Q00627Q00069A012Q002E00013Q00040F012Q002E00012Q004D000100013Q00121E000200076Q00033Q000500122Q000400093Q00202Q00040004000A00122Q000500033Q00122Q0006000B3Q00122Q000700033Q00122Q0008000B6Q00040008000200102Q0003000800040030930003000C000300105D0103000D3Q0012880104000F3Q0020E300040004000E0020E300040004001000105D0103000E00040030930003001100122Q004D000400024Q00FC0001000400022Q004D000200034Q0046010300013Q001216000400134Q00EE0002000400012Q004D000200043Q0030930002001400152Q000B012Q00013Q00013Q00053Q0003093Q00777269746566696C65030D3Q006F72696F6E5F62746E2E706E6703043Q0067616D6503073Q00482Q7470476574030E3Q00676574637573746F6D612Q736574000C3Q001288012Q00013Q001216000100023Q001288010200033Q00208D0002000200042Q004D00046Q00A1010200044Q00F75Q0001001288012Q00053Q001216000100024Q0051012Q00014Q0091017Q000B012Q00017Q00013Q0003083Q00506F736974696F6E010F4Q004D00016Q004601026Q009C2Q010002000200069A2Q01000E00013Q00040F012Q000E00012Q00E7000100014Q003F000100016Q00018Q000100023Q00202Q00013Q00014Q000100036Q000100053Q00202Q0001000100014Q000100044Q000B012Q00017Q00093Q0003083Q00506F736974696F6E03093Q004D61676E6974756465026Q00184003053Q005544696D322Q033Q006E657703013Q005803053Q005363616C6503063Q004F2Q6673657403013Q005901294Q004D00015Q00069A2Q01002800013Q00040F012Q002800012Q004D000100014Q004601026Q009C2Q010002000200069A2Q01002800013Q00040F012Q002800010020E300013Q00012Q004D000200024Q00322Q01000100020020E3000200010002000ED3000300100001000200040F012Q001000012Q00E7000200014Q00B8000200034Q004D000200033Q00069A0102002800013Q00040F012Q002800012Q004D000200043Q001245010300043Q00202Q0003000300054Q000400053Q00202Q00040004000600202Q0004000400074Q000500053Q00202Q00050005000600202Q00050005000800202Q0006000100064Q0005000500064Q000600053Q00202Q00060006000900202Q0006000600074Q000700053Q00202Q00070007000900202Q00070007000800202Q0008000100094Q0007000700084Q00030007000200102Q0002000100032Q000B012Q00019Q002Q0001104Q004D00015Q00069A2Q01000F00013Q00040F012Q000F00012Q004D000100014Q004601026Q009C2Q010002000200069A2Q01000F00013Q00040F012Q000F00012Q00E700016Q00B800016Q004D000100023Q0006572Q01000F0001000100040F012Q000F00012Q004D000100034Q00612Q01000100012Q000B012Q00017Q000B3Q0003063Q0069706169727303043Q007061676503073Q0056697369626C652Q033Q006261722Q033Q0062746E03163Q004261636B67726F756E645472616E73706172656E6379028Q00026Q00F03F030A3Q0054657874436F6C6F72332Q033Q007478742Q033Q006D757401224Q00427Q00122Q000100016Q000200016Q00010002000300044Q001F00010006AD0005000800013Q00040F012Q000800012Q001101066Q00E7000600013Q0020E300070005000200105D0107000300060020E300070005000400105D0107000300060020E300070005000500069A0106001300013Q00040F012Q00130001001216000800073Q000657010800140001000100040F012Q00140001001216000800083Q00105D0107000600080020E300070005000500069A0106001C00013Q00040F012Q001C00012Q004D000800023Q0020E300080008000A0006570108001E0001000100040F012Q001E00012Q004D000800023Q0020E300080008000B00105D01070009000800062B000100050001000200040F012Q000500012Q000B012Q00019Q002Q0002084Q004D00026Q0073000200023Q00069A0102000700013Q00040F012Q000700012Q0046010300024Q0046010400014Q00330003000200012Q000B012Q00017Q00013Q002Q033Q00736574020B4Q004D00026Q0073000200023Q00069A0102000800013Q00040F012Q000800010020E30003000200012Q0046010400014Q003300030002000100040F012Q000A00012Q004D000300014Q009E00033Q00012Q000B012Q00017Q00193Q00030A3Q005465787442752Q746F6E03043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q004540026Q00364003083Q00506F736974696F6E03103Q004261636B67726F756E64436F6C6F72332Q033Q006F2Q6603043Q0054657874034Q00030F3Q004175746F42752Q746F6E436F6C6F720100026Q00264003053Q004672616D65026Q003040026Q00084003063Q00436F6C6F72332Q033Q006E6577026Q00F03F030F3Q00426F7264657253697A65506978656C028Q00026Q0020402Q033Q0062746E03063Q0072656E646572023C4Q00C200025Q00122Q000300016Q00043Q000500122Q000500033Q00202Q00050005000400122Q000600053Q00122Q000700066Q00050007000200102Q00040002000500102Q0004000700014Q000500013Q00202Q00050005000900102Q00040008000500302Q0004000A000B00302Q0004000C000D4Q00058Q0002000500024Q000300026Q000400023Q00122Q0005000E6Q0003000500014Q00035Q00122Q0004000F6Q00053Q000400122Q000600033Q00202Q00060006000400122Q000700103Q00122Q000800106Q00060008000200102Q00050002000600122Q000600033Q00202Q00060006000400122Q000700113Q00122Q000800116Q00060008000200102Q00050007000600122Q000600123Q00202Q00060006001300122Q000700143Q00122Q000800143Q00122Q000900146Q00060009000200102Q00050008000600302Q0005001500164Q000600026Q0003000600024Q000400026Q000500033Q00122Q000600176Q0004000600014Q00043Q000100102Q0004001800020006B700053Q000100042Q004D3Q00034Q0046012Q00024Q004D3Q00014Q0046012Q00033Q00105D0104001900052Q00DA000400024Q000B012Q00013Q00013Q000D3Q0003063Q0043726561746503093Q0054772Q656E496E666F2Q033Q006E6577026Q33C33F03103Q004261636B67726F756E64436F6C6F72332Q033Q00612Q632Q033Q006F2Q6603043Q00506C617903083Q00506F736974696F6E03053Q005544696D32030A3Q0066726F6D4F2Q66736574026Q003740026Q000840012F4Q004D00015Q00208D0001000100012Q004D000300013Q001288010400023Q0020E3000400040003001216000500044Q009C0104000200022Q001301053Q000100069A012Q000E00013Q00040F012Q000E00012Q004D000600023Q0020E3000600060006000657010600100001000100040F012Q001000012Q004D000600023Q0020E300060006000700105D0105000500062Q00FC00010005000200208D0001000100082Q00330001000200012Q004D00015Q00208D0001000100012Q004D000300033Q001288010400023Q0020E3000400040003001216000500044Q009C0104000200022Q001301053Q000100069A012Q002500013Q00040F012Q002500010012880106000A3Q0020E300060006000B0012160007000C3Q0012160008000D4Q00FC0006000800020006570106002A0001000100040F012Q002A00010012880106000A3Q0020E300060006000B0012160007000D3Q0012160008000D4Q00FC00060008000200105D0105000900062Q00FC00010005000200208D0001000100082Q00330001000200012Q000B012Q00017Q00473Q00030A3Q005465787442752Q746F6E03043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q002Q4003103Q004261636B67726F756E64436F6C6F723303043Q006361726403163Q004261636B67726F756E645472616E73706172656E637903043Q0054657874030A3Q0054657874436F6C6F72332Q033Q006D757403043Q00466F6E7403043Q00456E756D030C3Q00476F7468616D4D656469756D03083Q005465787453697A65026Q002A40030F3Q004175746F42752Q746F6E436F6C6F720100030E3Q005465787458416C69676E6D656E7403043Q004C656674026Q00204003093Q00554950612Q64696E67030B3Q0050612Q64696E674C65667403043Q005544696D026Q002C4003053Q004672616D65030A3Q0066726F6D4F2Q66736574026Q00084003083Q00506F736974696F6E026Q0024C0026Q00E03F026Q001CC02Q033Q00612Q63030F3Q00426F7264657253697A65506978656C03073Q0056697369626C65027Q0040030E3Q005363726F2Q6C696E674672616D6503123Q005363726F2Q6C426172546869636B6E652Q7303143Q005363726F2Q6C426172496D616765436F6C6F723303043Q006C696E65030A3Q0043616E76617353697A6503133Q004175746F6D6174696343616E76617353697A65030D3Q004175746F6D6174696353697A6503013Q0059030C3Q0055494C6973744C61796F757403073Q0050612Q64696E6703093Q00536F72744F72646572030B3Q004C61796F75744F72646572030A3Q0050612Q64696E67546F70030C3Q0050612Q64696E675269676874030D3Q0050612Q64696E67426F2Q746F6D026Q0028402Q033Q0062746E2Q033Q0062617203043Q007061676503053Q00636172647303053Q006F7264657203053Q007461626C6503063Q00696E7365727403113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E65637403073Q0053656374696F6E03043Q004E6F746503063Q00546F2Q676C6503073Q004665617475726503063Q0042752Q746F6E03063Q00536C6964657203083Q0044726F70646F776E030B3Q004D756C746953656C65637401F74Q004D00015Q00121E000200016Q00033Q000900122Q000400033Q00202Q00040004000400122Q000500053Q00122Q000600063Q00122Q000700063Q00122Q000800076Q00040008000200102Q0003000200042Q004D000400013Q0020E300040004000900105D0103000800040030930003000A000500105D0103000B4Q004D000400013Q0020E300040004000D00105D0103000C00040012880104000F3Q0020E300040004000E0020E300040004001000105D0103000E00040030930003001100120030930003001300140012880104000F3Q0020E30004000400150020E300040004001600105D0103001500042Q004D000400024Q00FC0001000400022Q004D000200034Q0046010300013Q00129D000400176Q0002000400014Q00025Q00122Q000300186Q00043Q000100122Q0005001A3Q00202Q00050005000400122Q000600063Q00122Q0007001B6Q00050007000200105D0104001900052Q0046010500014Q00EE0002000500012Q004D00025Q0012160003001C4Q001301043Q0005001288010500033Q0020E300050005001D0012160006001E3Q0012160007001B4Q00FC00050007000200105D010400020005001288010500033Q0020E3000500050004001216000600063Q001216000700203Q001216000800213Q001216000900224Q00FC00050009000200105D0104001F00052Q004D000500013Q0020E300050005002300105D01040008000500303601040024000600302Q0004002500144Q000500016Q0002000500024Q000300036Q000400023Q00122Q000500266Q0003000500014Q00035Q00122Q000400274Q001301053Q0008001288010600033Q0020E3000600060004001216000700053Q001216000800063Q001299000900053Q00122Q000A00066Q0006000A000200102Q00050002000600302Q0005000A000500302Q00050024000600302Q00050028001E4Q000600013Q00202Q00060006002A00102Q00050029000600122Q000600033Q00202Q0006000600044Q00060001000200102Q0005002B000600122Q0006000F3Q00202Q00060006002D00202Q00060006002E00102Q0005002C000600302Q0005002500144Q000600046Q0003000600024Q00045Q00122Q0005002F6Q00063Q000200122Q0007001A3Q00202Q00070007000400122Q000800063Q00122Q000900176Q00070009000200102Q00060030000700122Q0007000F3Q00202Q00070007003100202Q00070007003200102Q0006003100074Q000700036Q0004000700014Q00045Q00122Q000500186Q00063Q000300122Q0007001A3Q00202Q00070007000400122Q000800063Q00122Q000900266Q00070009000200102Q00060033000700122Q0007001A3Q00202Q00070007000400122Q000800063Q00122Q000900176Q00070009000200102Q00060034000700122Q0007001A3Q00202Q00070007000400122Q000800063Q00122Q000900366Q00070009000200102Q0006003500074Q000700036Q0004000700014Q00043Q000500102Q00040037000100102Q00040038000200102Q0004003900034Q00055Q00102Q0004003A000500302Q0004003B000600122Q0005003C3Q00202Q00050005003D4Q000600056Q000700046Q00050007000100202Q00050001003E00202Q00050005003F0006B700073Q000100022Q004D3Q00064Q0046012Q00044Q00EE0005000700010006B700050001000100012Q0046012Q00043Q0006B700060002000100022Q0046012Q00054Q0046012Q00043Q0006B700070003000100022Q004D8Q004D3Q00013Q0006B700080004000100042Q004D8Q004D3Q00014Q0046012Q00034Q0046012Q00063Q00105D0104004000080006B700080005000100042Q004D8Q004D3Q00014Q0046012Q00034Q0046012Q00063Q00105D0104004100080006B700080006000100032Q004D3Q00074Q004D3Q00084Q004D3Q00093Q0006B700090007000100082Q004D8Q004D3Q00014Q0046012Q00034Q004D3Q00034Q0046012Q00074Q004D3Q000A4Q0046012Q00064Q0046012Q00083Q00105D0104004200090006B700090008000100092Q004D8Q004D3Q00014Q0046012Q00034Q004D3Q00034Q0046012Q00074Q004D3Q000B4Q004D3Q000A4Q0046012Q00064Q0046012Q00083Q00105D0104004300090006B700090009000100062Q004D8Q004D3Q00014Q0046012Q00034Q004D3Q00034Q0046012Q00074Q0046012Q00063Q00105D0104004400090006B70009000A0001000C2Q004D8Q004D3Q00014Q0046012Q00034Q004D3Q00034Q0046012Q00074Q004D3Q00074Q004D3Q000C4Q004D3Q000D4Q004D3Q000E4Q004D3Q000F4Q004D3Q00084Q0046012Q00063Q00105D0104004500090006B70009000B000100082Q004D8Q004D3Q00014Q0046012Q00034Q004D3Q00034Q0046012Q00074Q004D3Q00074Q004D3Q00084Q0046012Q00063Q00105D0104004600090006B70009000C000100082Q004D8Q004D3Q00014Q0046012Q00034Q004D3Q00034Q0046012Q00074Q004D3Q00074Q004D3Q00084Q0046012Q00063Q00105D0104004700092Q00DA000400024Q000B012Q00013Q000D8Q00044Q004D8Q004D000100014Q00333Q000200012Q000B012Q00017Q00023Q0003053Q006F72646572026Q00F03F00094Q004D8Q004D00015Q0020E30001000100010020AC2Q010001000200105D012Q000100012Q004D7Q0020E35Q00012Q00DA3Q00024Q000B012Q00017Q000A3Q00030B3Q004C61796F75744F7264657203053Q007461626C6503063Q00696E7365727403053Q00636172647303013Q006603013Q007303063Q00737472696E6703053Q006C6F776572034Q0003013Q002003174Q002Q01038Q00030001000200104Q0001000300122Q000300023Q00202Q0003000300034Q000400013Q00202Q0004000400044Q00053Q000200102Q000500053Q00122Q000600073Q00202Q00060006000800062Q0007000E0001000100040F012Q000E0001001216000700093Q0012160008000A3Q00068E000900120001000200040F012Q00120001001216000900094Q00870007000700092Q009C01060002000200105D0105000600062Q00EE0003000500012Q000B012Q00017Q00213Q0003093Q00546578744C6162656C03043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q00324003083Q00506F736974696F6E030A3Q0066726F6D4F2Q66736574026Q002C40026Q00224003163Q004261636B67726F756E645472616E73706172656E637903043Q0054657874030A3Q0054657874436F6C6F72332Q033Q0074787403043Q00466F6E7403043Q00456E756D030C3Q00476F7468616D4D656469756D03083Q005465787453697A65030E3Q005465787458416C69676E6D656E7403043Q004C656674030C3Q00546578745472756E6361746503053Q004174456E64026Q003A40026Q003C40034Q002Q033Q006D757403063Q00476F7468616D026Q002640030B3Q00546578745772612Q7065642Q01030E3Q005465787459416C69676E6D656E742Q033Q00546F7004544Q00DD00045Q00122Q000500016Q00063Q000900122Q000700033Q00202Q00070007000400122Q000800056Q000900033Q00122Q000A00063Q00122Q000B00076Q0007000B000200102Q00060002000700122Q000700033Q00202Q00070007000900122Q0008000A3Q00122Q0009000B6Q00070009000200102Q00060008000700302Q0006000C000500102Q0006000D00014Q000700013Q00202Q00070007000F00102Q0006000E000700122Q000700113Q00202Q00070007001000202Q00070007001200102Q00060010000700302Q00060013000A00122Q000700113Q00202Q00070007001400202Q00070007001500102Q00060014000700122Q000700113Q00202Q00070007001600202Q00070007001700102Q0006001600074Q00078Q0004000700014Q00045Q00122Q000500016Q00063Q000B00122Q000700033Q00202Q00070007000400122Q000800056Q000900033Q00122Q000A00063Q00122Q000B00186Q0007000B000200102Q00060002000700122Q000700033Q00202Q00070007000900122Q0008000A3Q00122Q000900196Q00070009000200102Q00060008000700302Q0006000C000500062Q0007003A0001000200040F012Q003A00010012160007001A3Q00105D0106000D00072Q004D000700013Q0020E300070007001B00105D0106000E0007001288010700113Q0020E30007000700100020E300070007001C00105D01060010000700309300060013001D0030930006001E001F001288010700113Q0020E30007000700140020E300070007001500105D010600140007001288010700113Q0020E30007000700200020E300070007002100105D010600200007001288010700113Q0020E30007000700160020E300070007001700105D0106001600072Q004601076Q0051010400074Q009101046Q000B012Q00017Q00153Q0003093Q00546578744C6162656C03043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q00384003163Q004261636B67726F756E645472616E73706172656E637903043Q0054657874030A3Q0054657874436F6C6F72332Q033Q006D757403043Q00466F6E7403043Q00456E756D030C3Q00476F7468616D4D656469756D03083Q005465787453697A65026Q002840030E3Q005465787458416C69676E6D656E7403043Q004C656674030E3Q005465787459416C69676E6D656E7403063Q00426F2Q746F6D034Q0001264Q004D00015Q00121E000200016Q00033Q000800122Q000400033Q00202Q00040004000400122Q000500053Q00122Q000600063Q00122Q000700063Q00122Q000800076Q00040008000200102Q00030002000400309300030008000500105D010300094Q004D000400013Q0020E300040004000B00105D0103000A00040012880104000D3Q0020E300040004000C0020E300040004000E00105D0103000C00040030930003000F00100012880104000D3Q0020E30004000400110020E300040004001200105D0103001100040012880104000D3Q0020E30004000400130020E300040004001400105D0103001300042Q004D000400024Q00FC0001000400022Q004D000200034Q0046010300013Q0012D2000400153Q00122Q000500156Q0002000500014Q000100028Q00017Q00193Q0003093Q00546578744C6162656C03043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q003040030D3Q004175746F6D6174696353697A6503043Q00456E756D03013Q005903163Q004261636B67726F756E645472616E73706172656E637903043Q0054657874030A3Q0054657874436F6C6F72332Q033Q006D757403043Q00466F6E7403063Q00476F7468616D03083Q005465787453697A65026Q002840030B3Q00546578745772612Q7065642Q01030E3Q005465787458416C69676E6D656E7403043Q004C656674030E3Q005465787459416C69676E6D656E742Q033Q00546F70034Q00012B4Q004D00015Q00121E000200016Q00033Q000A00122Q000400033Q00202Q00040004000400122Q000500053Q00122Q000600063Q00122Q000700063Q00122Q000800076Q00040008000200102Q000300020004001288010400093Q0020E30004000400080020E300040004000A00105D0103000800040030930003000B000500105D0103000C4Q004D000400013Q0020E300040004000E00105D0103000D0004001288010400093Q0020E300040004000F0020E300040004001000105D0103000F0004003093000300110012003093000300130014001288010400093Q0020E30004000400150020E300040004001600105D010300150004001288010400093Q0020E30004000400170020E30004000400180010FE0003001700044Q000400026Q0001000400024Q000200036Q000300016Q00045Q00122Q000500196Q0002000500014Q000100028Q00017Q000C3Q0003053Q0067726F757003043Q0069734F6E2Q033Q007365742Q033Q0062746E03113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E6563742Q0103053Q007061697273010003063Q0072656E64657203043Q007461736B03053Q00646566657204474Q001301043Q000100105D0104000100032Q00E700055Q0006B700063Q000100062Q0046012Q00054Q004D8Q0046012Q00014Q0046017Q004D3Q00014Q0046012Q00023Q0006B700070001000100012Q0046012Q00053Q00105D0104000200070006B700070002000100022Q0046012Q00054Q0046012Q00063Q00105D0104000300070020E300073Q00040020E300070007000500208D0007000700060006B700090003000100052Q0046012Q00054Q0046012Q00034Q004D3Q00024Q0046012Q00044Q0046012Q00064Q00CC0007000900014Q000700026Q0007000100044Q00078Q00070007000100262Q000700220001000700040F012Q002200012Q001101056Q00E7000500013Q00069A0105003900013Q00040F012Q0039000100069A0103003900013Q00040F012Q00390001001288010700084Q004D000800024Q00B200070002000900040F012Q003700010006AD000B00370001000400040F012Q003700010020E3000C000B0001000627000C00370001000300040F012Q003700010020E3000C000B00022Q0065010C0001000200069A010C003700013Q00040F012Q003700012Q00E700056Q004D000C5Q00202C000C0001000900062B0007002B0001000200040F012Q002B00010020E300073Q000A2Q0046010800054Q003300070002000100069A0105004500013Q00040F012Q0045000100069A0102004500013Q00040F012Q004500010012880107000B3Q0020E300070007000C0006B700080004000100012Q0046012Q00024Q00330007000200012Q00DA000400024Q000B012Q00013Q00053Q00023Q0003063Q0072656E64657203053Q007063612Q6C01193Q00069A012Q000500013Q00040F012Q000500012Q00E7000100013Q0006572Q0100060001000100040F012Q000600012Q00E700016Q00B800016Q004D000100014Q004D000200024Q004D00036Q009E0001000200032Q004D000100033Q0020E30001000100012Q004D00026Q00330001000200012Q004D000100044Q00612Q01000100012Q004D000100053Q00069A2Q01001800013Q00040F012Q001800010012882Q0100024Q004D000200054Q004D00036Q00EE0001000300012Q000B012Q00019Q003Q00034Q004D8Q00DA3Q00024Q000B012Q00019Q002Q0001074Q004D00015Q0006AD0001000600013Q00040F012Q000600012Q004D000100014Q004601026Q00330001000200012Q000B012Q00017Q00043Q0003053Q00706169727303053Q0067726F757003043Q0069734F6E2Q033Q00736574001F4Q004D7Q000657012Q001A0001000100040F012Q001A00012Q004D3Q00013Q00069A012Q001A00013Q00040F012Q001A0001001288012Q00014Q004D000100024Q00B23Q0002000200040F012Q001800012Q004D000500033Q0006AD000400180001000500040F012Q001800010020E30005000400022Q004D000600013Q000627000500180001000600040F012Q001800010020E30005000400032Q006501050001000200069A0105001800013Q00040F012Q001800010020E30005000400042Q00E700066Q003300050002000100062B3Q000A0001000200040F012Q000A00012Q004D3Q00044Q004D00016Q00A7000100014Q00333Q000200012Q000B012Q00017Q00013Q0003053Q007063612Q6C00053Q001288012Q00014Q004D00016Q00E7000200014Q00EE3Q000200012Q000B012Q00017Q000E3Q0003053Q004672616D6503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q004D4003103Q004261636B67726F756E64436F6C6F723303043Q0063617264026Q002440026Q005440026Q004DC0026Q00E03F026Q0026C005324Q004D00055Q00121E000600016Q00073Q000200122Q000800033Q00202Q00080008000400122Q000900053Q00122Q000A00063Q00122Q000B00063Q00122Q000C00076Q0008000C000200102Q0007000200082Q004D000800013Q0020E300080008000900105D0107000800082Q004D000800024Q00FC0005000800022Q004D000600034Q0046010700053Q0012160008000A4Q00EE0006000800012Q004D000600044Q0046010700054Q004601086Q0046010900013Q001216000A000B4Q00FC0006000A00022Q004D000700054Q0046010800053Q001288010900033Q0020E3000900090004001216000A00053Q001216000B000C3Q001216000C000D3Q001216000D000E4Q00A10109000D4Q000400073Q00022Q004D000800064Q0046010900054Q0046010A6Q0046010B00014Q00EE0008000B00012Q004D000800074Q0046010900074Q0046010A00024Q0069010B00036Q000C00046Q0008000C00024Q000900066Q000800038Q00017Q00103Q0003053Q004672616D6503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q004D4003103Q004261636B67726F756E64436F6C6F723303043Q0063617264026Q00244003093Q004465736C696761646F026Q005440026Q004DC0026Q00E03F026Q0026C0034Q0004374Q004D00045Q00121E000500016Q00063Q000200122Q000700033Q00202Q00070007000400122Q000800053Q00122Q000900063Q00122Q000A00063Q00122Q000B00076Q0007000B000200102Q0006000200072Q004D000700013Q0020E300070007000900105D0106000800072Q004D000700024Q00FC0004000700022Q004D000500034Q0046010600043Q0012160007000A4Q00EE0005000700012Q004D000500044Q0046010600044Q004601075Q0012160008000B3Q0012160009000C4Q00FC0005000900022Q004D000600053Q0006B700073Q000100012Q0046012Q00054Q00990106000100074Q000600066Q000700043Q00122Q000800033Q00202Q00080008000400122Q000900053Q00122Q000A000D3Q00122Q000B000E3Q00122Q000C000F6Q0008000C6Q00063Q00024Q000700076Q000800046Q00095Q00122Q000A00106Q0007000A00014Q000700086Q000800066Q000900013Q0006B7000A0001000100022Q0046012Q00054Q0046012Q00034Q0046010B00024Q00510107000B4Q009101076Q000B012Q00013Q00023Q00013Q0003043Q005465787401034Q004D00015Q00105D2Q0100014Q000B012Q00017Q00023Q0003043Q005465787403093Q004465736C696761646F010B3Q000657012Q00040001000100040F012Q000400012Q004D00015Q0030930001000100022Q004D000100013Q00069A2Q01000A00013Q00040F012Q000A00012Q004D000100014Q004601026Q00330001000200012Q000B012Q00017Q00223Q0003053Q004672616D6503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q004D4003103Q004261636B67726F756E64436F6C6F723303043Q0063617264026Q002440025Q00806140030A3Q005465787442752Q746F6E030A3Q0066726F6D4F2Q66736574026Q005940026Q003C4003083Q00506F736974696F6E025Q00805CC0026Q00E03F026Q002CC02Q033Q00612Q6303043Q005465787403083Q004578656375746172030A3Q0054657874436F6C6F723303063Q00436F6C6F723303043Q00466F6E7403043Q00456E756D030C3Q00476F7468616D4D656469756D03083Q005465787453697A65026Q002840030F3Q004175746F42752Q746F6E436F6C6F720100026Q00204003113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E65637404514Q004D00045Q00121E000500016Q00063Q000200122Q000700033Q00202Q00070007000400122Q000800053Q00122Q000900063Q00122Q000A00063Q00122Q000B00076Q0007000B000200102Q0006000200072Q004D000700013Q0020E300070007000900105D0106000800072Q004D000700024Q00FC0004000700022Q004D000500034Q0046010600043Q0012160007000A4Q00EE0005000700012Q004D000500044Q0046010600044Q009600078Q000800013Q00122Q0009000B6Q0005000900024Q00065Q00122Q0007000C6Q00083Q000800122Q000900033Q00202Q00090009000D00122Q000A000E3Q001216000B000F4Q00FC0009000B000200105D010800020009001288010900033Q0020E3000900090004001216000A00053Q001216000B00113Q001216000C00123Q001216000D00134Q00FC0009000D000200105D0108001000092Q004D000900013Q0020E300090009001400105D01080008000900068E000900310001000200040F012Q00310001001216000900163Q00105D010800150009001288010900183Q0020E3000900090004001216000A00053Q001216000B00053Q001216000C00054Q00FC0009000C000200105D0108001700090012880109001A3Q0020E30009000900190020E300090009001B00105D0108001900090030930008001C001D0030930008001E001F2Q0046010900044Q00FC0006000900022Q004D000700034Q0046010800063Q001216000900204Q00EE0007000900010020E300070006002100208D0007000700220006B700093Q000100012Q0046012Q00034Q00EE0007000900012Q004D000700054Q0046010800044Q004601096Q0046010A00014Q00EE0007000A00012Q00DA000500024Q000B012Q00013Q00013Q00013Q0003053Q007063612Q6C00043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q003A3Q0003053Q004672616D6503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00025Q0080504003103Q004261636B67726F756E64436F6C6F723303043Q0063617264026Q002440026Q00594003073Q0054657874426F78030A3Q0066726F6D4F2Q66736574026Q004F40026Q00384003083Q00506F736974696F6E026Q0053C0026Q00204003023Q00626703043Q005465787403083Q00746F737472696E67030A3Q0054657874436F6C6F72332Q033Q0074787403043Q00466F6E7403043Q00456E756D030C3Q00476F7468616D4D656469756D03083Q005465787453697A65026Q00284003103Q00436C656172546578744F6E466F6375730100026Q001840026Q003CC0026Q002C40026Q004B402Q033Q006F2Q66030F3Q00426F7264657253697A65506978656C026Q00084003043Q006D61746803053Q00636C616D702Q033Q00612Q63030B3Q00416E63686F72506F696E7403073Q00566563746F7232026Q00E03F03063Q00436F6C6F723303063Q005A496E646578027Q0040030A3Q005465787442752Q746F6E026Q002CC0026Q003640026Q001C40026Q00474003163Q004261636B67726F756E645472616E73706172656E6379034Q00030A3Q00496E707574426567616E03073Q00436F2Q6E656374030C3Q00496E7075744368616E676564030A3Q00496E707574456E64656403093Q00466F6375734C6F737406FD4Q001201065Q00122Q000700016Q00083Q000200122Q000900033Q00202Q00090009000400122Q000A00053Q00122Q000B00063Q00122Q000C00063Q00122Q000D00076Q0009000D000200102Q0008000200094Q000900013Q00202Q00090009000900102Q0008000800094Q000900026Q0006000900024Q000700036Q000800063Q00122Q0009000A6Q0007000900014Q000700046Q000800066Q00098Q000A00013Q00122Q000B000B6Q0007000B00014Q00075Q00122Q0008000C6Q00093Q000800122Q000A00033Q00202Q000A000A000D00122Q000B000E3Q00122Q000C000F6Q000A000C000200102Q00090002000A00122Q000A00033Q00202Q000A000A000400122Q000B00053Q00122Q000C00113Q00122Q000D00063Q00122Q000E00126Q000A000E000200102Q00090010000A4Q000A00013Q00202Q000A000A001300102Q00090008000A00122Q000A00156Q000B00056Q000B000B00044Q000A0002000200102Q00090014000A4Q000A00013Q00202Q000A000A001700102Q00090016000A00122Q000A00193Q00202Q000A000A001800202Q000A000A001A00102Q00090018000A00302Q0009001B001C00302Q0009001D001E4Q000A00066Q0007000A00024Q000800036Q000900073Q00122Q000A001F6Q0008000A00014Q00085Q00122Q000900016Q000A3Q000400122Q000B00033Q00202Q000B000B000400122Q000C00053Q00122Q000D00203Q00122Q000E00063Q00122Q000F001F6Q000B000F000200102Q000A0002000B00122Q000B00033Q00202Q000B000B000D00122Q000C00213Q0012A4000D00226Q000B000D000200102Q000A0010000B4Q000B00013Q00202Q000B000B002300102Q000A0008000B00302Q000A002400064Q000B00066Q0008000B00024Q000900034Q0046010A00083Q001216000B00254Q00EE0009000B0001001288010900263Q0020E30009000900272Q004D000A00054Q0073000A000A00042Q0032010A000A00022Q0032010B000300022Q0040010A000A000B001216000B00063Q001216000C00054Q00FC0009000C00022Q004D000A5Q001216000B00014Q0013010C3Q0003001288010D00033Q0020E3000D000D00042Q0046010E00093Q001216000F00063Q001216001000053Q0012A4001100066Q000D0011000200102Q000C0002000D4Q000D00013Q00202Q000D000D002800102Q000C0008000D00302Q000C002400064Q000D00086Q000A000D00024Q000B00034Q0046010C000A3Q00129D000D00256Q000B000D00014Q000B5Q00122Q000C00016Q000D3Q000600122Q000E00033Q00202Q000E000E000D00122Q000F001C3Q00122Q0010001C6Q000E0010000200105D010D0002000E001288010E002A3Q0020E3000E000E0004001216000F002B3Q0012160010002B4Q00FC000E0010000200105D010D0029000E001288010E00033Q0020E3000E000E00042Q0046010F00093Q001216001000063Q0012160011002B3Q001216001200064Q00FC000E0012000200101A010D0010000E00122Q000E002C3Q00202Q000E000E000400122Q000F00053Q00122Q001000053Q00122Q001100056Q000E0011000200102Q000D0008000E00302Q000D0024000600302Q000D002D002E2Q0046010E00084Q00FC000B000E00022Q004D000C00034Q0046010D000B3Q001216000E001F4Q00EE000C000E00012Q004D000C5Q00121E000D002F6Q000E3Q000400122Q000F00033Q00202Q000F000F000400122Q001000053Q00122Q001100303Q00122Q001200063Q00122Q001300316Q000F0013000200102Q000E0002000F001288010F00033Q0020E3000F000F000D001216001000323Q001216001100334Q00FC000F0011000200105D010E0010000F003093000E00340005003093000E001400352Q0046010F00064Q00FC000C000F00020020F6000D00020005002681010D00C00001000600040F012Q00C000010020F6000D00030005002681010D00C00001000600040F012Q00C000012Q0032010D00030002000E6C000A00C10001000D00040F012Q00C100012Q0011010D6Q00E7000D00013Q0006B7000E3Q000100092Q0046012Q00024Q0046012Q00034Q0046012Q000D4Q004D3Q00054Q0046012Q00044Q0046012Q000A4Q0046012Q000B4Q0046012Q00074Q0046012Q00054Q00E7000F5Q0020E30010000C003600208D0010001000370006B700120001000100062Q004D3Q00064Q0046012Q000F4Q0046012Q000E4Q0046012Q00024Q0046012Q00034Q0046012Q00084Q00EE0010001200012Q004D001000074Q004D001100083Q0020E300110011003800208D0011001100370006B700130002000100062Q0046012Q000F4Q004D3Q00094Q0046012Q000E4Q0046012Q00024Q0046012Q00034Q0046012Q00084Q00A1011100134Q00F700103Q00012Q004D001000074Q004D001100083Q0020E300110011003900208D0011001100370006B700130003000100032Q0046012Q000F4Q004D3Q00064Q004D3Q000A4Q00A1011100134Q00F700103Q00010020E300100007003A00208D0010001000370006B700120004000100052Q0046012Q00074Q0046012Q000E4Q004D3Q000A4Q004D3Q00054Q0046012Q00044Q00EE0010001200012Q004D0010000B4Q0046011100064Q004601126Q0046011300014Q00EE0010001300012Q000B012Q00013Q00053Q000E3Q0003043Q006D61746803053Q00636C616D7003053Q00666C2Q6F72026Q00E03F026Q00594003043Q0053697A6503053Q005544696D322Q033Q006E6577028Q00026Q00F03F03083Q00506F736974696F6E03043Q005465787403083Q00746F737472696E6703053Q007063612Q6C013E3Q0012882Q0100013Q0020E30001000100022Q004601026Q004D00036Q004D000400014Q00FC0001000400022Q0046012Q00014Q004D000100023Q00069A2Q01001000013Q00040F012Q001000010012882Q0100013Q0020E30001000100030020AC01023Q00042Q009C2Q01000200022Q0046012Q00013Q00040F012Q001600010012882Q0100013Q0020EB00010001000300202Q00023Q000500202Q0002000200044Q00010002000200204Q000100052Q004D000100034Q004D000200044Q009E000100024Q004D00016Q00322Q013Q00012Q004D000200014Q004D00036Q00320102000200032Q00402Q01000100022Q004D000200053Q001288010300073Q0020E30003000300082Q0046010400013Q001216000500093Q0012160006000A3Q001216000700094Q00FC00030007000200105D0102000600032Q004D000200063Q001288010300073Q0020E30003000300082Q0046010400013Q001216000500093Q001216000600043Q001216000700094Q00FC00030007000200105D0102000B00032Q004D000200073Q0012880103000D4Q004601046Q009C01030002000200105D0102000C00032Q004D000200083Q00069A0102003D00013Q00040F012Q003D00010012880102000E4Q004D000300084Q004601046Q00EE0002000400012Q000B012Q00017Q00083Q0003043Q006D61746803053Q00636C616D7003083Q00506F736974696F6E03013Q005803103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A65028Q00026Q00F03F011F4Q004D00016Q004601026Q009C2Q010002000200069A2Q01001E00013Q00040F012Q001E00012Q00E7000100014Q00B8000100014Q004D000100025Q00010200036Q000300046Q000400036Q00030003000400122Q000400013Q00202Q00040004000200202Q00053Q000300202Q0005000500044Q000600053Q00202Q00060006000500202Q0006000600044Q0005000500064Q000600053Q00202Q00060006000600202Q0006000600044Q00050005000600122Q000600073Q00122Q000700086Q0004000700024Q0003000300044Q0002000200034Q0001000200012Q000B012Q00017Q00083Q0003043Q006D61746803053Q00636C616D7003083Q00506F736974696F6E03013Q005803103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A65028Q00026Q00F03F01204Q004D00015Q00069A2Q01001F00013Q00040F012Q001F00012Q004D000100014Q004601026Q009C2Q010002000200069A2Q01001F00013Q00040F012Q001F00012Q004D000100025Q00010200036Q000300046Q000400036Q00030003000400122Q000400013Q00202Q00040004000200202Q00053Q000300202Q0005000500044Q000600053Q00202Q00060006000500202Q0006000600044Q0005000500064Q000600053Q00202Q00060006000600202Q0006000600044Q00050005000600122Q000600073Q00122Q000700086Q0004000700024Q0003000300044Q0002000200034Q0001000200012Q000B012Q00019Q002Q00010D4Q004D00015Q00069A2Q01000C00013Q00040F012Q000C00012Q004D000100014Q004601026Q009C2Q010002000200069A2Q01000C00013Q00040F012Q000C00012Q00E700016Q00B800016Q004D000100024Q00612Q01000100012Q000B012Q00017Q00033Q0003083Q00746F6E756D62657203043Q005465787403083Q00746F737472696E6700143Q0012E23Q00016Q00015Q00202Q0001000100026Q0002000200064Q000C00013Q00040F012Q000C00012Q004D000100014Q00A501028Q0001000200014Q000100026Q00010001000100044Q001300012Q004D00015Q0012E1000200036Q000300036Q000400046Q0003000300044Q00020002000200102Q0001000200022Q000B012Q00017Q00363Q0003053Q004672616D6503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q004D4003103Q004261636B67726F756E64436F6C6F723303043Q006361726403103Q00436C69707344657363656E64616E74732Q01026Q002440026Q006440030A3Q005465787442752Q746F6E030A3Q0066726F6D4F2Q66736574025Q00806040026Q003C4003083Q00506F736974696F6E025Q004062C0026Q002E402Q033Q006F2Q6603043Q0054657874034Q00030A3Q0054657874436F6C6F72332Q033Q0074787403043Q00466F6E7403043Q00456E756D030C3Q00476F7468616D4D656469756D03083Q005465787453697A65026Q002840030F3Q004175746F42752Q746F6E436F6C6F720100030C3Q00546578745472756E6361746503053Q004174456E64026Q002040030E3Q005363726F2Q6C696E674672616D65026Q0034C0026Q00504003163Q004261636B67726F756E645472616E73706172656E6379030F3Q00426F7264657253697A65506978656C03123Q005363726F2Q6C426172546869636B6E652Q73026Q000840030A3Q0043616E76617353697A6503133Q004175746F6D6174696343616E76617353697A65030D3Q004175746F6D6174696353697A6503013Q0059030C3Q0055494C6973744C61796F757403073Q0050612Q64696E6703043Q005544696D03073Q006F7074696F6E73026Q001840030A3Q007365744F7074696F6E7303113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E656374069C4Q004D00065Q00121E000700016Q00083Q000300122Q000900033Q00202Q00090009000400122Q000A00053Q00122Q000B00063Q00122Q000C00063Q00122Q000D00076Q0009000D000200102Q0008000200092Q0002010900013Q00202Q00090009000900102Q00080008000900302Q0008000A000B4Q000900026Q0006000900024Q000700036Q000800063Q00122Q0009000C6Q0007000900012Q004D000700044Q0034000800066Q00098Q000A00013Q00122Q000B000D6Q0007000B00014Q00075Q00122Q0008000E6Q00093Q000900122Q000A00033Q00202Q000A000A000F001216000B00103Q001216000C00114Q00FC000A000C000200105D01090002000A001288010A00033Q0020E3000A000A0004001216000B00053Q001216000C00133Q001216000D00063Q001216000E00144Q00FC000A000E000200105D01090012000A2Q004D000A00013Q002044000A000A001500102Q00090008000A00302Q0009001600174Q000A00013Q00202Q000A000A001900102Q00090018000A00122Q000A001B3Q00202Q000A000A001A00202Q000A000A001C00102Q0009001A000A0030930009001D001E0030930009001F0020001288010A001B3Q0020E3000A000A00210020E3000A000A002200105D01090021000A2Q0046010A00064Q00FC0007000A00022Q004D000800034Q0046010900073Q001216000A00234Q00EE0008000A00012Q004D00085Q00121E000900246Q000A3Q000700122Q000B00033Q00202Q000B000B000400122Q000C00053Q00122Q000D00253Q00122Q000E00063Q00122Q000F00066Q000B000F000200102Q000A0002000B001288010B00033Q0020E3000B000B000F001216000C000C3Q001216000D00264Q00FC000B000D000200105D010A0012000B003093000A00270005003093000A00280006003093000A0029002A001288010B00033Q0020E3000B000B00042Q0065010B0001000200105D010A002B000B001288010B001B3Q0020E3000B000B002D0020E3000B000B002E00105D010A002C000B2Q0046010B00064Q00FC0008000B00022Q004D00095Q001216000A002F4Q0013010B3Q0001001288010C00313Q0020E3000C000C0004001216000D00063Q001216000E002A4Q00FC000C000E000200105D010B0030000C2Q0046010C00084Q00EE0009000C00012Q001301093Q000100105D0109003200022Q00E7000A5Q00068E000B00720001000500040F012Q00720001001216000B00333Q0006B7000C3Q000100012Q0046012Q00073Q0006B7000D0001000100052Q0046012Q00094Q0046012Q000B4Q0046012Q00084Q0046012Q00064Q0046012Q000A3Q0006B7000E00020001000C2Q0046012Q00094Q0046012Q00084Q004D8Q004D3Q00014Q004D3Q00034Q004D3Q00054Q0046012Q00034Q0046012Q000C4Q0046012Q000A4Q0046012Q000D4Q004D3Q00064Q0046012Q00043Q00105D01090034000E0020E3000E0007003500208D000E000E00360006B700100003000100022Q0046012Q000A4Q0046012Q000D4Q00EE000E001000012Q0046010E000C4Q004D000F00054Q0073000F000F00032Q0033000E000200010020E3000E000900342Q0046010F00024Q0033000E000200012Q004D000E00074Q0046010F00064Q004601106Q0046011100014Q00EE000E001100012Q00DA000900024Q000B012Q00013Q00043Q00063Q0003043Q005465787400034Q0003083Q00746F737472696E6703043Q003Q207603083Q004E6F6E653Q2076010F4Q004D00015Q00267B3Q000C0001000200040F012Q000C000100267B3Q000C0001000300040F012Q000C0001001288010200044Q002900038Q00020002000200122Q000300056Q00020002000300062Q0002000D0001000100040F012Q000D0001001216000200063Q00105D2Q01000100022Q000B012Q00017Q000C3Q0003043Q006D6174682Q033Q006D696E03073Q006F7074696F6E7303043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F026Q0034C0028Q00026Q003D40026Q005240026Q004D4000213Q0012D93Q00013Q00206Q00024Q00015Q00202Q0001000100034Q000100016Q000200018Q000200024Q000100023Q00122Q000200053Q00202Q00020002000600122Q000300073Q00122Q000400083Q00122Q000500093Q00202Q00063Q000A4Q00020006000200102Q0001000400024Q000100033Q00122Q000200053Q00202Q00020002000600122Q000300073Q00122Q000400093Q00122Q000500096Q000600043Q00062Q0006001D00013Q00040F012Q001D00010020AF01063Q000A0010090106000B00060006570106001E0001000100040F012Q001E00010012160006000C4Q00FC00020006000200105D2Q01000400022Q000B012Q00017Q001D3Q0003073Q006F7074696F6E7303063Q00697061697273030B3Q004765744368696C6472656E2Q033Q00497341030A3Q005465787442752Q746F6E03073Q0044657374726F7903043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F026Q0018C0028Q00026Q003A4003103Q004261636B67726F756E64436F6C6F723303023Q00626703043Q005465787403083Q00746F737472696E67030A3Q0054657874436F6C6F72332Q033Q0074787403043Q00466F6E7403043Q00456E756D03063Q00476F7468616D03083Q005465787453697A65026Q002840030F3Q004175746F42752Q746F6E436F6C6F720100026Q00184003113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E65637401484Q00BE00015Q00102Q000100013Q00122Q000100026Q000200013Q00202Q0002000200034Q000200036Q00013Q000300044Q000F000100208D000600050004001216000800054Q00FC00060008000200069A0106000F00013Q00040F012Q000F000100208D0006000500062Q003300060002000100062B000100080001000200040F012Q000800010012882Q0100024Q004601026Q00B200010002000300040F012Q004300012Q004D000600023Q00121E000700056Q00083Q000700122Q000900083Q00202Q00090009000900122Q000A000A3Q00122Q000B000B3Q00122Q000C000C3Q00122Q000D000D6Q0009000D000200102Q0008000700092Q004D000900033Q0020E300090009000F00105D0108000E0009001288010900114Q0046010A00054Q009C01090002000200105D0108001000092Q004D000900033Q0020E300090009001300105D010800120009001288010900153Q0020E30009000900140020E300090009001600105D01080014000900309300080017001800309300080019001A2Q004D000900014Q00FC0006000900022Q004D000700044Q0046010800063Q0012160009001B4Q00EE0007000900010020E300070006001C00208D00070007001D0006B700093Q000100082Q004D3Q00054Q004D3Q00064Q0046012Q00054Q004D3Q00074Q004D3Q00084Q004D3Q00094Q004D3Q000A4Q004D3Q000B4Q00EE0007000900012Q000F00045Q00062B000100150001000200040F012Q001500012Q004D000100094Q00612Q01000100012Q000B012Q00013Q00013Q00013Q0003053Q007063612Q6C00154Q00E09Q00000100016Q000200028Q000100026Q00036Q000100028Q000200019Q006Q00048Q00058Q000100016Q00068Q000100016Q00073Q00064Q001400013Q00040F012Q00140001001288012Q00014Q004D000100074Q004D000200024Q00EE3Q000200012Q000B012Q00019Q003Q00064Q004D8Q00A78Q00B88Q004D3Q00014Q0061012Q000100012Q000B012Q00017Q003A3Q0003053Q004672616D6503043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F028Q00026Q004D4003103Q004261636B67726F756E64436F6C6F723303043Q006361726403103Q00436C69707344657363656E64616E74732Q01026Q002440025Q00C06740030A3Q005465787442752Q746F6E030A3Q0066726F6D4F2Q66736574026Q006440026Q003C4003083Q00506F736974696F6E025Q00C065C0026Q002E402Q033Q006F2Q6603043Q0054657874034Q00030A3Q0054657874436F6C6F72332Q033Q0074787403043Q00466F6E7403043Q00456E756D030C3Q00476F7468616D4D656469756D03083Q005465787453697A65026Q002840030F3Q004175746F42752Q746F6E436F6C6F720100030C3Q00546578745472756E6361746503053Q004174456E64026Q002040030E3Q005363726F2Q6C696E674672616D65026Q0034C0026Q00504003163Q004261636B67726F756E645472616E73706172656E6379030F3Q00426F7264657253697A65506978656C03123Q005363726F2Q6C426172546869636B6E652Q73026Q000840030A3Q0043616E76617353697A6503133Q004175746F6D6174696343616E76617353697A65030D3Q004175746F6D6174696353697A6503013Q0059030C3Q0055494C6973744C61796F757403073Q0050612Q64696E6703043Q005544696D026Q00144003063Q00697061697273026Q0018C0026Q003A4003023Q00626703063Q00476F7468616D026Q00184003113Q004D6F75736542752Q746F6E31436C69636B03073Q00436F2Q6E65637405C14Q004D00055Q00121E000600016Q00073Q000300122Q000800033Q00202Q00080008000400122Q000900053Q00122Q000A00063Q00122Q000B00063Q00122Q000C00076Q0008000C000200102Q0007000200082Q0002010800013Q00202Q00080008000900102Q00070008000800302Q0007000A000B4Q000800026Q0005000800024Q000600036Q000700053Q00122Q0008000C6Q0006000800012Q004D000600044Q0034000700056Q00088Q000900013Q00122Q000A000D6Q0006000A00014Q00065Q00122Q0007000E6Q00083Q000900122Q000900033Q00202Q00090009000F001216000A00103Q001216000B00114Q00FC0009000B000200105D010800020009001288010900033Q0020E3000900090004001216000A00053Q001216000B00133Q001216000C00063Q001216000D00144Q00FC0009000D000200105D0108001200092Q004D000900013Q00204400090009001500102Q00080008000900302Q0008001600174Q000900013Q00202Q00090009001900102Q00080018000900122Q0009001B3Q00202Q00090009001A00202Q00090009001C00102Q0008001A00090030930008001D001E0030930008001F00200012880109001B3Q0020E30009000900210020E300090009002200105D0108002100092Q0046010900054Q00FC0006000900022Q004D000700034Q0046010800063Q001216000900234Q00EE0007000900012Q004D00075Q00121E000800246Q00093Q000700122Q000A00033Q00202Q000A000A000400122Q000B00053Q00122Q000C00253Q00122Q000D00063Q00122Q000E00066Q000A000E000200102Q00090002000A001288010A00033Q0020E3000A000A000F001216000B000C3Q001216000C00264Q00FC000A000C000200105D01090012000A00309300090027000500309300090028000600309300090029002A001288010A00033Q0020E3000A000A00042Q0065010A0001000200105D0109002B000A001288010A001B3Q0020E3000A000A002D0020E3000A000A002E00105D0109002C000A2Q0046010A00054Q00FC0007000A00022Q004D00085Q0012160009002F4Q0013010A3Q0001001288010B00313Q0020E3000B000B0004001216000C00063Q001216000D002A4Q00FC000B000D000200105D010A0030000B2Q0046010B00074Q00EE0008000B00012Q00E700085Q00068E000900700001000400040F012Q00700001001216000900323Q0006B7000A3Q000100032Q0046012Q00024Q004D3Q00054Q0046012Q00063Q0006B7000B0001000100052Q0046012Q00024Q0046012Q00094Q0046012Q00074Q0046012Q00054Q0046012Q00083Q001288010C00334Q0046010D00024Q00B2000C0002000E00040F012Q00AF00012Q004D00115Q00121E0012000E6Q00133Q000700122Q001400033Q00202Q00140014000400122Q001500053Q00122Q001600343Q00122Q001700063Q00122Q001800356Q00140018000200102Q0013000200142Q004D001400013Q00204400140014003600102Q00130008001400302Q0013001600174Q001400013Q00202Q00140014001900102Q00130018001400122Q0014001B3Q00202Q00140014001A00202Q00140014003700102Q0013001A00140030930013001D001E0030930013001F00202Q0046011400074Q00FC0011001400022Q004D001200034Q0046011300113Q001216001400384Q00EE0012001400010006B700120002000100042Q0046012Q00114Q004D3Q00054Q0046012Q00104Q004D3Q00014Q0046011300124Q00610113000100010020E300130011003900208D00130013003A0006B700150003000100062Q004D3Q00054Q0046012Q00104Q0046012Q00124Q0046012Q000A4Q004D3Q00064Q0046012Q00034Q00EE0013001500012Q000F00116Q000F000F5Q00062B000C007E0001000200040F012Q007E00010020E3000C0006003900208D000C000C003A0006B7000E0004000100022Q0046012Q00084Q0046012Q000B4Q00EE000C000E00012Q0046010C000A4Q0061010C000100012Q0046010C000B4Q0061010C000100012Q004D000C00074Q0046010D00054Q0046010E6Q0046010F00014Q00EE000C000F00012Q000B012Q00013Q00053Q000B3Q0003063Q006970616972732Q033Q006B657903053Q007461626C6503063Q00696E7365727403053Q006C6162656C03043Q0054657874028Q0003063Q004E656E68756D03063Q00636F6E63617403023Q002C2003043Q003Q207600214Q0013016Q0012882Q0100014Q004D00026Q00B200010002000300040F012Q000F00012Q004D000600013Q0020E30007000500022Q007300060006000700069A0106000F00013Q00040F012Q000F0001001288010600033Q0020E30006000600042Q004601075Q0020E30008000500052Q00EE00060008000100062B000100050001000200040F012Q000500012Q004D000100024Q00D000025Q002681010200180001000700040F012Q00180001001216000200083Q0006570102001D0001000100040F012Q001D0001001288010200033Q0020E30002000200092Q004601035Q0012160004000A4Q00FC0002000400020012160003000B4Q008700020002000300105D2Q01000600022Q000B012Q00017Q000B3Q0003043Q006D6174682Q033Q006D696E03043Q0053697A6503053Q005544696D322Q033Q006E6577026Q00F03F026Q0034C0028Q00026Q003D40026Q005240026Q004D4000203Q001274012Q00013Q00206Q00024Q00018Q000100016Q000200018Q000200024Q000100023Q00122Q000200043Q00202Q00020002000500122Q000300063Q001216000400073Q001279000500083Q00202Q00063Q00094Q00020006000200102Q0001000300024Q000100033Q00122Q000200043Q00202Q00020002000500122Q000300063Q00122Q000400083Q00122Q000500084Q004D000600043Q00069A0106001C00013Q00040F012Q001C00010020AF01063Q00090010090106000A00060006570106001D0001000100040F012Q001D00010012160006000B4Q00FC00020006000200105D2Q01000300022Q000B012Q00017Q00083Q0003043Q00546578742Q033Q006B657903053Q005B785D2Q2003073Q005B3Q205D2Q2003053Q006C6162656C030A3Q0054657874436F6C6F72332Q033Q00612Q632Q033Q00747874001E4Q004D8Q004D000100014Q004D000200023Q0020E30002000200022Q007300010001000200069A2Q01000A00013Q00040F012Q000A0001001216000100033Q0006572Q01000B0001000100040F012Q000B0001001216000100044Q004D000200023Q0020230002000200054Q00010001000200104Q000100019Q004Q000100016Q000200023Q00202Q0002000200024Q00010001000200062Q0001001A00013Q00040F012Q001A00012Q004D000100033Q0020E30001000100070006572Q01001C0001000100040F012Q001C00012Q004D000100033Q0020E300010001000800105D012Q000600012Q000B012Q00017Q00023Q002Q033Q006B657903053Q007063612Q6C00164Q004D8Q004D000100013Q0020E30001000100012Q004D00026Q004D000300013Q0020E30003000300012Q00730002000200032Q00A7000200024Q009E3Q000100022Q004D3Q00024Q0061012Q000100012Q00B4012Q00038Q000100016Q00048Q000100016Q00053Q00064Q001500013Q00040F012Q00150001001288012Q00024Q004D000100054Q00333Q000200012Q000B012Q00019Q003Q00064Q004D8Q00A78Q00B88Q004D3Q00014Q0061012Q000100012Q000B012Q00017Q000D3Q0003063Q00737472696E6703053Q006C6F77657203043Q0054657874034Q0003063Q0069706169727303053Q00636172647303013Q006603073Q0056697369626C6503013Q007303013Q002003043Q0066696E64026Q00F03F2Q00264Q004D7Q000657012Q00040001000100040F012Q000400012Q000B012Q00013Q001288012Q00013Q0020E35Q00022Q004D000100013Q0020E30001000100030006572Q01000B0001000100040F012Q000B0001001216000100044Q009C012Q000200020012152Q0100056Q00025Q00202Q0002000200064Q00010002000300044Q002300010020E300060005000700267B3Q00210001000400040F012Q002100010020E300070005000900267B000700200001000A00040F012Q00200001001288010700013Q0020E300070007000B0020E30008000500092Q004601095Q001216000A000C4Q00E7000B00014Q00FC0007000B0002002681010700210001000D00040F012Q002100012Q001101076Q00E7000700013Q00105D01060008000700062B000100110001000200040F012Q001100012Q000B012Q00019Q003Q00044Q004D8Q004D000100014Q00333Q000200012Q000B012Q00017Q00123Q0003063Q00506172656E7403043Q006D6174682Q033Q006D6178028Q0003053Q00666C2Q6F7203023Q006F7303053Q00636C6F636B025Q0018F540025Q0020AC40026Q004E4003043Q005465787403063Q00737472696E6703063Q00666F726D617403313Q00436F6E65637461646F206861202564206469612873292C202530326420682C2025303264206D696E20652025303264207303263Q00436F6E65637461646F206861202530326420682C2025303264206D696E20652025303264207303043Q007461736B03043Q0077616974026Q00F03F00414Q004D7Q000657012Q00400001000100040F012Q004000012Q004D3Q00013Q0020E35Q000100069A012Q004000013Q00040F012Q00400001001288012Q00023Q0020E35Q0003001216000100043Q001288010200023Q0020E3000200020005001288010300063Q0020E30003000300072Q00650103000100022Q004D000400024Q00320103000300042Q00DE000200034Q00045Q00020012882Q0100023Q0020E30001000100050020EA00023Q00082Q009C2Q0100020002001288010200023Q0020E30002000200050020F600033Q00080020EA0003000300092Q009C010200020002001288010300023Q0020E30003000300050020F600043Q00090020EA00040004000A2Q009C0103000200020020F600043Q000A2Q004D000500033Q00069A0105003B00013Q00040F012Q003B0001000ED3000400320001000100040F012Q003200012Q004D000500033Q0012550106000C3Q00202Q00060006000D00122Q0007000E6Q000800016Q000900026Q000A00036Q000B00046Q0006000B000200102Q0005000B000600044Q003B00012Q004D000500033Q0012880106000C3Q0020E300060006000D0012160007000F4Q0046010800024Q0046010900034Q0046010A00044Q00FC0006000A000200105D0105000B0006001288010500103Q0020E3000500050011001216000600124Q003300050002000100040F014Q00012Q000B012Q00017Q00033Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696400094Q004D7Q0020E35Q00010006210001000700013Q00040F012Q0007000100208D00013Q0002001216000300034Q00FC0001000300022Q00DA000100024Q000B012Q00017Q00033Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727400094Q004D7Q0020E35Q00010006210001000700013Q00040F012Q0007000100208D00013Q0002001216000300034Q00FC0001000300022Q00DA000100024Q000B012Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403073Q0052656D6F74657303063Q00436F2Q6D465F000B4Q00F87Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q00040F012Q0009000100208D00013Q0001001216000300034Q00FC0001000300022Q00DA000100024Q000B012Q00017Q00013Q0003053Q007063612Q6C00144Q004D00016Q00652Q01000100020006572Q0100060001000100040F012Q000600012Q0062000200024Q00DA000200024Q001301026Q000C01036Q004300023Q0001001288010300013Q0006B700043Q000100022Q0046012Q00014Q0046012Q00024Q00B200030002000400069A0103001100013Q00040F012Q001100012Q00DA000400024Q0062000500054Q00DA000500024Q000B012Q00013Q00013Q00023Q00030C3Q00496E766F6B6553657276657203063Q00756E7061636B00084Q004D7Q00208D5Q0001001288010200024Q004D000300014Q00DE000200034Q003E8Q0091017Q000B012Q00017Q00033Q0003053Q007063612Q6C03083Q00746F6E756D626572026Q00F03F000E3Q001288012Q00013Q0006B700013Q000100012Q004D8Q00B23Q0002000100069A012Q000B00013Q00040F012Q000B0001001288010200024Q0046010300014Q009C0102000200020006570102000C0001000100040F012Q000C0001001216000200034Q00DA000200024Q000B012Q00013Q00013Q00033Q0003043Q004461746103053Q004C6576656C03053Q0056616C756500064Q00CA7Q00206Q000100206Q000200206Q00036Q00028Q00017Q00063Q0003063Q00737472696E6703053Q006C6F77657203043Q006773756203083Q00746F737472696E6703053Q005B5E25615D034Q00010D3Q0012882Q0100013Q0020E3000100010002001288010200013Q0020E3000200020003001288010300044Q004601046Q009C010300020002001216000400053Q001216000500064Q00FC0002000500022Q00512Q0100024Q00912Q016Q000B012Q00017Q00023Q00028Q0003053Q007063612Q6C000A4Q004D7Q000ED30001000400013Q00040F012Q000400012Q000B012Q00013Q001288012Q00023Q0006B700013Q000100022Q004D3Q00014Q004D8Q00333Q000200012Q000B012Q00013Q00013Q000B3Q0003063Q0069706169727303093Q00506C61796572477569030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q00546578744C6162656C03063Q00737472696E6703053Q006D6174636803043Q005465787403093Q00252D5365612825642903083Q00746F6E756D626572029Q001E3Q0012803Q00016Q00015Q00202Q00010001000200202Q0001000100034Q000100029Q00000200044Q001B000100208D000500040004001216000700054Q00FC00050007000200069A0105001B00013Q00040F012Q001B0001001288010500063Q0020E30005000500070020E3000600040008001216000700094Q00FC00050007000200069A0105001B00013Q00040F012Q001B00010012880106000A4Q0046010700054Q009C010600020002000657010600190001000100040F012Q001900010012160006000B4Q00B8000600014Q000B012Q00013Q00062B3Q00070001000200040F012Q000700012Q000B012Q00017Q00073Q002Q033Q0049734103083Q00426173655061727403053Q004D6F64656C030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274030B3Q005072696D6172795061727403163Q0046696E6446697273744368696C645768696368497341011B3Q00208D00013Q0001001216000300024Q00FC00010003000200069A2Q01000600013Q00040F012Q000600012Q00DA3Q00023Q00208D00013Q0001001216000300034Q00FC00010003000200069A2Q01001800013Q00040F012Q0018000100208D00013Q0004001216000300054Q00FC0001000300020006572Q0100170001000100040F012Q001700010020E300013Q00060006572Q0100170001000100040F012Q0017000100208D00013Q0007001216000300024Q00E7000400014Q00FC0001000400022Q00DA000100024Q0062000100014Q00DA000100024Q000B012Q00017Q00043Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030C3Q005F576F726C644F726967696E03093Q004C6F636174696F6E73000B3Q001288012Q00013Q00208D5Q0002001216000200034Q00FC3Q000200020006210001000900013Q00040F012Q0009000100208D00013Q0002001216000300044Q00FC0001000300022Q00DA000100024Q000B012Q00017Q00073Q0003063Q00697061697273030B3Q004765744368696C6472656E03063Q00737472696E6703043Q0066696E6403043Q004E616D65026Q00F03F03053Q007063612Q6C01234Q004D00016Q00652Q01000100020006572Q0100060001000100040F012Q000600012Q0062000200024Q00DA000200023Q001288010200013Q00208D0003000100022Q00DE000300044Q003501023Q000400040F012Q001E0001001288010700033Q0020970007000700044Q000800013Q00202Q0009000600054Q0008000200024Q00095Q00122Q000A00066Q000B00016Q0007000B000200062Q0007001D00013Q00040F012Q001D0001001288010700073Q0006B700083Q000100012Q0046012Q00064Q00B200070002000800069A0107001D00013Q00040F012Q001D00012Q00DA000800024Q000F00055Q00062B0002000B0001000200040F012Q000B00012Q0062000200024Q00DA000200024Q000B012Q00013Q00013Q00023Q0003083Q004765745069766F7403083Q00506F736974696F6E00064Q00CD7Q00206Q00016Q0002000200206Q00026Q00028Q00017Q001E3Q00026Q00F03F03063Q00434672616D652Q033Q006E657703083Q00506F736974696F6E03093Q004D61676E697475646503043Q006D6174682Q033Q006D696E026Q0069402Q033Q006D6178026Q00244002B81E85EB51B89E3F03023Q006F7303053Q00636C6F636B03093Q0074772Q656E4D6F646503053Q0054772Q656E03063Q0043726561746503093Q0054772Q656E496E666F03043Q00456E756D030B3Q00456173696E675374796C6503063Q004C696E65617203093Q00436F6D706C6574656403073Q00436F2Q6E65637403043Q00506C6179026Q00084003053Q007063612Q6C03043Q007461736B03043Q0077616974027B14AE47E17AA43F030A3Q00446973636F2Q6E65637403093Q0048656172746265617403924Q004D00035Q0020AC0103000300012Q00B800036Q004D00036Q004D000400014Q00650104000100020006570104000A0001000100040F012Q000A00012Q00E700056Q00DA000500023Q0020E3000500040002001288010600023Q0020E30006000600030020E300073Q00042Q009C0106000200020020E30007000500042Q00320107000500072Q00600006000600070020E30007000500040020E30008000600042Q00320107000700080020E30007000700050026950007001B0001000100040F012Q001B000100105D0104000200062Q00E7000800014Q00DA000800023Q001288010800063Q0020E300080008000700068E000900200001000100040F012Q00200001001216000900083Q001216000A00084Q00FC0008000A00022Q00462Q0100083Q001288010800063Q0020E3000800080009001288010900063Q0020E30009000900092Q0046010A00013Q001216000B000A4Q00FC0009000B00022Q0040010900070009001216000A000B4Q00FC0008000A00020012880109000C3Q0020E300090009000D2Q00650109000100022Q00E7000A6Q00E7000B6Q004D000C00023Q0020E3000C000C000E002681010C00750001000F00040F012Q007500012Q004D000C00033Q00208D000C000C00102Q0046010E00043Q001288010F00113Q0020E3000F000F00032Q0046011000083Q001288011100123Q0020E30011001100130020E30011001100142Q00FC000F001100022Q001301103Q000100105D0110000200062Q00FC000C001000020020E3000D000C001500208D000D000D00160006B7000F3Q000100012Q0046012Q000A4Q00FC000D000F000200208D000E000C00172Q0033000E00020001000657010A006E0001000100040F012Q006E0001001288010E000C3Q0020E3000E000E000D2Q0065010E000100022Q0032010E000E00090020AC010F00080018000676010E006E0001000F00040F012Q006E00012Q004D000E00043Q000657010E00630001000100040F012Q006300012Q004D000E5Q000627000300630001000E00040F012Q0063000100069A0102005F00013Q00040F012Q005F00012Q0046010E00024Q0065010E0001000200069A010E006300013Q00040F012Q006300012Q004D000E00014Q0065010E00010002000657010E00690001000100040F012Q006900012Q00E7000B00013Q001288010E00193Q0006B7000F0001000100012Q0046012Q000C4Q0033000E0002000100040F012Q006E0001001288010E001A3Q0020E3000E000E001B001216000F001C4Q0033000E0002000100040F012Q004A000100208D000E000D001D2Q0033000E00020001000621000E00730001000A00040F012Q007300012Q00A7000E000B4Q00DA000E00024Q000F000C6Q0062000C000C4Q004D000D00053Q0020E3000D000D001E00208D000D000D00160006B7000F00020001000C2Q004D3Q00014Q004D3Q00044Q0046012Q00034Q004D8Q0046012Q00024Q0046012Q00094Q0046012Q00084Q0046012Q000B4Q0046012Q000C4Q0046012Q00054Q0046012Q00064Q0046012Q000A4Q00FC000D000F00022Q0046010C000D3Q000657010A00900001000100040F012Q00900001000657010B00900001000100040F012Q00900001001288010D001A3Q0020E3000D000D001B2Q0061010D0001000100040F012Q008800012Q00DA000A00024Q000B012Q00013Q00038Q00034Q00E73Q00014Q00B88Q000B012Q00017Q00013Q0003063Q0043616E63656C00044Q004D7Q00208D5Q00012Q00333Q000200012Q000B012Q00017Q00093Q0003023Q006F7303053Q00636C6F636B026Q001040030A3Q00446973636F2Q6E65637403043Q006D6174682Q033Q006D696E026Q00F03F03063Q00434672616D6503043Q004C657270003A4Q004D8Q0065012Q000100022Q004D000100013Q0006572Q01001B0001000100040F012Q001B00012Q004D000100024Q004D000200033Q0006270001001B0001000200040F012Q001B000100069A012Q001B00013Q00040F012Q001B00012Q004D000100043Q00069A2Q01001200013Q00040F012Q001200012Q004D000100044Q00652Q010001000200069A2Q01001B00013Q00040F012Q001B00010012882Q0100013Q0020E30001000100022Q00652Q01000100022Q004D000200054Q00322Q01000100022Q004D000200063Q0020AC010200020003000676010200210001000100040F012Q002100012Q00E7000100014Q00672Q0100076Q000100083Q00202Q0001000100044Q0001000200016Q00013Q0012882Q0100053Q0020E3000100010006001288010200013Q0020E30002000200022Q00650102000100022Q004D000300054Q00320102000200032Q004D000300064Q0040010200020003001216000300074Q00FC0001000300022Q004D000200093Q00208D0002000200092Q004D0004000A4Q0046010500014Q00FC00020005000200105D012Q00080002000EF3000700390001000100040F012Q003900012Q00E7000200014Q00B80002000B4Q004D000200083Q00208D0002000200042Q00330002000200012Q000B012Q00017Q00083Q0003083Q006661726D4469737403093Q00706F734D6574686F6403063Q00426568696E6403073Q00566563746F72332Q033Q006E6577028Q00026Q00084003053Q0042656C6F7702253Q0006572Q0100040001000100040F012Q000400012Q004D00025Q0020E30001000200012Q004D00025Q0020E3000200020002002681010200100001000300040F012Q00100001001288010200043Q0020E3000200020005001216000300063Q001216000400074Q0046010500014Q00FC0002000500022Q003301023Q00022Q00DA000200024Q004D00025Q0020E30002000200020026810102001C0001000800040F012Q001C0001001288010200043Q00201701020002000500122Q000300066Q000400013Q00122Q000500066Q0002000500024Q00023Q00024Q000200023Q001288010200043Q0020F000020002000500122Q000300066Q000400013Q00122Q000500066Q0002000500024Q00023Q00024Q000200028Q00017Q00143Q0003023Q006F7303053Q00636C6F636B03043Q006D61746803053Q00636C616D7002FCA9F1D24D62903F029A5Q99B93F03083Q00506F736974696F6E03093Q004D61676E6974756465026Q00694003043Q00556E697403073Q00666163654D6F6203063Q00434672616D6503063Q006C2Q6F6B417403073Q00566563746F72332Q033Q006E657703013Q005803013Q005903013Q005A03163Q00412Q73656D626C794C696E65617256656C6F63697479028Q0002414Q004D00026Q0065010200010002000657010200060001000100040F012Q000600012Q00E700036Q00DA000300023Q001288010300013Q00207A0103000300024Q00030001000200122Q000400033Q00202Q0004000400044Q000500016Q00050003000500122Q000600053Q00122Q000700066Q0004000700024Q000300013Q00202Q0005000200074Q00063Q000500202Q00070006000800102Q0008000900044Q00095Q00062Q0008001B0001000700040F012Q001B00010020E3000A0006000A2Q0060000A000A00082Q003301090005000A2Q004D000A00023Q0020E3000A000A000B00069A010A002D00013Q00040F012Q002D000100069A2Q01002D00013Q00040F012Q002D0001001288010A000C3Q0020E3000A000A000D2Q0046010B00093Q001288010C000E3Q0020E3000C000C000F0020E3000D000100100020E3000E000900110020E3000F000100122Q00A1010C000F4Q0004000A3Q000200105D0102000C000A00040F012Q00370001001288010A000C3Q0020E3000A000A000F2Q0046010B00094Q009C010A000200020020E3000B0002000C0020E3000C0002000C0020E3000C000C00072Q0032010B000B000C2Q0060000A000A000B00105D0102000C000A001288010A000E3Q0020E3000A000A000F001216000B00143Q001216000C00143Q001216000D00144Q00FC000A000D000200105D01020013000A2Q00E7000A00014Q00DA000A00024Q000B012Q00017Q000E3Q0003063Q006E6F636C697003093Q0043686172616374657203063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103083Q004261736550617274030A3Q0043616E436F2Q6C6964650100030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403163Q00412Q73656D626C794C696E65617256656C6F6369747903073Q00566563746F72332Q033Q006E6577029Q002A4Q004D7Q0020E35Q000100069A012Q000A00013Q00040F012Q000A00012Q004D3Q00013Q000657012Q000B0001000100040F012Q000B00012Q004D3Q00023Q000657012Q000B0001000100040F012Q000B00012Q000B012Q00014Q004D3Q00033Q0020E35Q0002000657012Q00100001000100040F012Q001000012Q000B012Q00013Q0012882Q0100033Q00208D00023Q00042Q00DE000200034Q00352Q013Q000300040F012Q001B000100208D000600050005001216000800064Q00FC00060008000200069A0106001B00013Q00040F012Q001B000100309300050007000800062B000100150001000200040F012Q0015000100208D00013Q00090012160003000A4Q00FC00010003000200069A2Q01002900013Q00040F012Q002900010012880102000C3Q0020E300020002000D0012160003000E3Q0012160004000E3Q0012160005000E4Q00FC00020005000200105D2Q01000B00022Q000B012Q00017Q00083Q0003043Q0068616B6903023Q006F7303053Q00636C6F636B026Q00144003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403073Q004861734275736F03043Q004275736F001E4Q004D7Q0020E35Q0001000657012Q00050001000100040F012Q000500012Q000B012Q00013Q001288012Q00023Q00201F5Q00036Q000100024Q000100019Q00000100264Q000D0001000400040F012Q000D00012Q000B012Q00013Q001288012Q00023Q0020E35Q00032Q0065012Q000100022Q00B83Q00014Q004D3Q00023Q0020E35Q000500069A012Q001D00013Q00040F012Q001D000100208D00013Q0006001216000300074Q00FC0001000300020006572Q01001D0001000100040F012Q001D00012Q004D000100033Q001216000200084Q00330001000200012Q000B012Q00017Q00093Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C03073Q00542Q6F6C54697003063Q0069706169727303083Q004261636B7061636B030B3Q004765744368696C6472656E2Q033Q0049734103093Q004571756970542Q6F6C01284Q006800015Q00202Q0001000100014Q000200016Q00020001000200062Q0001000800013Q00040F012Q00080001000657010200090001000100040F012Q000900012Q000B012Q00013Q00208D000300010002001216000500034Q00FC00030005000200069A0103001200013Q00040F012Q001200010020E30004000300040006270004001200013Q00040F012Q001200012Q000B012Q00013Q001288010400054Q004D00055Q0020E300050005000600208D0005000500072Q00DE000500064Q003501043Q000600040F012Q0025000100208D000900080008001216000B00034Q00FC0009000B000200069A0109002500013Q00040F012Q002500010020E30009000800040006270009002500013Q00040F012Q0025000100208D0009000200092Q0046010B00084Q00EE0009000B00012Q000B012Q00013Q00062B000400190001000200040F012Q001900012Q000B012Q00017Q00013Q0003063Q00776561706F6E00074Q004F019Q002Q000100016Q00016Q000100023Q00202Q0001000100016Q000200016Q00017Q000A3Q0003093Q00776F726B7370616365030D3Q0043752Q72656E7443616D657261030C3Q0056696577706F727453697A6503073Q00566563746F72322Q033Q006E6577026Q008940025Q00207C4003013Q0058027Q004003013Q005900123Q001288012Q00013Q0020E35Q000200069A012Q000700013Q00040F012Q000700010020E300013Q00030006572Q01000C0001000100040F012Q000C00010012882Q0100043Q0020E3000100010005001216000200063Q001216000300074Q00FC0001000300020020E30002000100080020EA0002000200090020E300030001000A0020EA0003000300092Q0036000200034Q000B012Q00017Q00083Q0003073Q0056697369626C6503103Q004162736F6C757465506F736974696F6E030C3Q004162736F6C75746553697A6503013Q0058026Q00244003013Q0059026Q004940010002204Q004D00025Q0020E3000200020001000657010200050001000100040F012Q000500012Q000B012Q00014Q004D00025Q0020E30002000200022Q004D00035Q0020E30003000300030020E30004000200040020780004000400050006F20004001F00013Q00040F012Q001F00010020E30004000200040020E30005000300042Q00330104000400050020AC0104000400050006F23Q001F0001000400040F012Q001F00010020E30004000200060020780004000400050006F20004001F0001000100040F012Q001F00010020E30004000200060020E30005000300062Q00330104000400050020AC0104000400070006F20001001F0001000400040F012Q001F00012Q004D00045Q0030930004000100082Q000B012Q00017Q00013Q0003053Q007063612Q6C00164Q004D7Q00069A012Q001100013Q00040F012Q001100012Q004D3Q00014Q00B13Q000100012Q004D000200024Q004601036Q0046010400014Q00EE000200040001001288010200013Q0006B700033Q000100032Q004D8Q0046017Q0046012Q00014Q00330002000200012Q000F7Q00040F012Q00150001001288012Q00013Q0006B700010001000100012Q004D3Q00034Q00333Q000200012Q000B012Q00013Q00023Q00033Q0003143Q0053656E644D6F75736542752Q746F6E4576656E74028Q0003043Q0067616D6500134Q004D7Q00208D5Q00012Q004D000200014Q004D000300023Q001216000400024Q00E7000500013Q001288010600033Q001216000700024Q00EE3Q000700012Q004D7Q00208D5Q00012Q004D000200014Q004D000300023Q001216000400024Q00E700055Q001288010600033Q001216000700024Q00EE3Q000700012Q000B012Q00017Q00063Q0003113Q0043617074757265436F6E74726F2Q6C6572030C3Q00436C69636B42752Q746F6E3103073Q00566563746F72322Q033Q006E6577025Q00208C40025Q00407F40000C4Q00E67Q00206Q00016Q000200019Q0000206Q000200122Q000200033Q00202Q00020002000400122Q000300053Q00122Q000400066Q000200044Q00F75Q00012Q000B012Q00017Q00013Q0003053Q007063612Q6C00053Q001288012Q00013Q0006B700013Q000100012Q004D8Q00333Q000200012Q000B012Q00013Q00013Q00043Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C03083Q004163746976617465000C4Q004D7Q0020E35Q00010006210001000700013Q00040F012Q0007000100208D00013Q0002001216000300034Q00FC00010003000200069A2Q01000B00013Q00040F012Q000B000100208D0002000100042Q00330002000200012Q000B012Q00017Q00013Q0003053Q007063612Q6C00063Q001288012Q00013Q0006B700013Q000100022Q004D8Q004D3Q00014Q00333Q000200012Q000B012Q00013Q00013Q00053Q00030C3Q0057616974466F724368696C64030D3Q00506C6179657253637269707473026Q002440030F3Q00436F6D6261744672616D65776F726B03073Q007265717569726500124Q0042016Q00206Q000100122Q000200023Q00122Q000300038Q0003000200062Q0001000B00013Q00040F012Q000B000100208D00013Q0001001216000300043Q001216000400034Q00FC00010004000200069A2Q01001100013Q00040F012Q00110001001288010200054Q0046010300014Q009C0102000200022Q00B8000200014Q000B012Q00017Q00013Q0003053Q007063612Q6C000A3Q001288012Q00013Q0006B700013Q000100012Q004D8Q00B23Q0002000100069A012Q000700013Q00040F012Q000700012Q00DA000100024Q0062000200024Q00DA000200024Q000B012Q00013Q00013Q00013Q0003103Q00616374697665436F6E74726F2Q6C657200074Q004D7Q00069A012Q000500013Q00040F012Q000500012Q004D7Q0020E35Q00012Q00DA3Q00024Q000B012Q00017Q00023Q0003063Q0061637469766503053Q007063612Q6C00104Q004D8Q0065012Q0001000200069A012Q000D00013Q00040F012Q000D00010020E300013Q000100069A2Q01000D00013Q00040F012Q000D00010012882Q0100023Q0006B700023Q000100012Q0046017Q00330001000200012Q00E7000100014Q00DA000100024Q00E700016Q00DA000100024Q000B012Q00013Q00013Q00043Q0003103Q0074696D65546F4E657874412Q7461636B028Q00030B3Q00686974626F78547269656403063Q00612Q7461636B00084Q004D7Q0030933Q000100022Q004D7Q0030933Q000300022Q004D7Q00208D5Q00042Q00333Q000200012Q000B012Q00017Q00023Q0003063Q0061637469766503053Q007063612Q6C00144Q004D8Q0065012Q000100020006210001000500013Q00040F012Q000500010020E300013Q000100069A2Q01001100013Q00040F012Q00110001001288010200023Q0006B700033Q000100012Q0046012Q00014Q0033000200020001001288010200023Q0006B700030001000100012Q0046012Q00014Q00330002000200012Q00E7000200014Q00DA000200024Q00E700026Q00DA000200024Q000B012Q00013Q00023Q00023Q0003083Q00612Q7461636B6572030D3Q00686974536572766572436F6465000E4Q004D7Q0020E35Q000100069A012Q000D00013Q00040F012Q000D00012Q004D7Q0020E35Q00010020E35Q000200069A012Q000D00013Q00040F012Q000D00012Q004D7Q0020E35Q000100208D5Q00022Q00333Q000200012Q000B012Q00017Q00023Q0003063Q00776561706F6E03063Q00612Q7461636B000E4Q004D7Q0020E35Q000100069A012Q000D00013Q00040F012Q000D00012Q004D7Q0020E35Q00010020E35Q000200069A012Q000D00013Q00040F012Q000D00012Q004D7Q0020E35Q000100208D5Q00022Q00333Q000200012Q000B012Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403073Q004D6F64756C65732Q033Q004E657401104Q00F800015Q00202Q00010001000100122Q000300026Q00010003000200062Q000200090001000100040F012Q0009000100208D000200010001001216000400034Q00FC0002000400020006210003000E0001000200040F012Q000E000100208D0003000200012Q004601056Q00FC0003000500022Q00DA000300024Q000B012Q00017Q00053Q0003043Q004E616D65034Q0003063Q00737472696E672Q033Q00737562026Q00F03F011E4Q004D00015Q0006572Q0100050001000100040F012Q000500012Q00E7000100014Q00DA000100024Q004D000100014Q004D00026Q009C2Q01000200022Q004D000200013Q00069A012Q000E00013Q00040F012Q000E00010020E300033Q00010006570103000F0001000100040F012Q000F0001001216000300024Q009C01020002000200267B0001001A0001000200040F012Q001A0001001288010300033Q0020E30003000300042Q0046010400023Q001216000500054Q00D0000600014Q00FC0003000600020006AD0003001B0001000100040F012Q001B00012Q001101036Q00E7000300014Q00DA000300024Q000B012Q00017Q000E3Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403073Q00456E656D69657303063Q00697061697273030B3Q004765744368696C6472656E03153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403103Q0048756D616E6F6964522Q6F745061727403063Q004865616C7468028Q0003083Q00506F736974696F6E03093Q004D61676E697475646503053Q007461626C6503063Q00696E7365727401324Q00C500015Q00122Q000200013Q00202Q00020002000200122Q000400036Q0002000400024Q00038Q00030001000200062Q0002000B00013Q00040F012Q000B00010006570103000C0001000100040F012Q000C00012Q00DA000100023Q001288010400043Q00208D0005000200052Q00DE000500064Q003501043Q000600040F012Q002E000100208D0009000800060012BB000B00076Q0009000B000200202Q000A0008000200122Q000C00086Q000A000C000200062Q0009002E00013Q00040F012Q002E000100069A010A002E00013Q00040F012Q002E00010020E3000B00090009000ED3000A002E0001000B00040F012Q002E00012Q004D000B00014Q0046010C00084Q009C010B0002000200069A010B002E00013Q00040F012Q002E00010020E3000B000A000B0020E3000C0003000B2Q0032010B000B000C0020E3000B000B000C0006F2000B002E00013Q00040F012Q002E0001001288010B000D3Q0020E3000B000B000E2Q0046010C00014Q0046010D00084Q00EE000B000D000100062B000400110001000200040F012Q001100012Q00DA000100024Q000B012Q00017Q00033Q0003113Q0052452F5265676973746572412Q7461636B030E3Q0052452F526567697374657248697403053Q007063612Q6C01184Q004D00015Q001216000200014Q009C2Q01000200022Q004D00025Q001216000300024Q009C01020002000200069A2Q01000A00013Q00040F012Q000A00010006570102000C0001000100040F012Q000C00012Q00E700036Q00DA000300024Q00E700035Q001288010400033Q0006B700053Q000100062Q004D3Q00014Q0046017Q004D3Q00024Q0046012Q00014Q0046012Q00024Q0046012Q00034Q00330004000200012Q00DA000300024Q000B012Q00013Q00013Q000B3Q0003063Q00697061697273026Q004E40030E3Q0046696E6446697273744368696C6403043Q004865616403103Q0048756D616E6F6964522Q6F745061727403053Q007461626C6503063Q00696E73657274026Q00F03F027Q0040030A3Q0046697265536572766572029Q00464Q0013017Q0062000100013Q001288010200014Q004D00035Q001216000400024Q00DE000300044Q003501023Q000400040F012Q001D000100208D000700060003001216000900044Q00FC000700090002000657010700100001000100040F012Q0010000100208D000700060003001216000900054Q00FC00070009000200069A0107001D00013Q00040F012Q001D0001001288010800063Q0020E30008000800072Q004601096Q0013010A00024Q0046010B00064Q0046010C00074Q0023010A000200012Q00EE0008000A00010006572Q01001D0001000100040F012Q001D00012Q00462Q0100073Q00062B000200080001000200040F012Q000800012Q004D000200013Q00069A0102003800013Q00040F012Q00380001001288010200014Q004D000300014Q00B200020002000400040F012Q003600010020E300070006000800069A0107003600013Q00040F012Q003600012Q004D000700023Q0020E30008000600082Q009C01070002000200069A0107003600013Q00040F012Q00360001001288010700063Q00208C0107000700074Q00088Q000900066Q00070009000100062Q000100360001000100040F012Q003600010020E300010006000900062B000200260001000200040F012Q0026000100069A2Q01004500013Q00040F012Q004500012Q004D000200033Q0020DF00020002000A00122Q0004000B6Q0002000400014Q000200043Q00202Q00020002000A4Q000400016Q00058Q0002000500014Q000200016Q000200054Q000B012Q00017Q00023Q0003053Q007063612Q6C03053Q00726561647900083Q001288012Q00013Q0006B700013Q000100022Q004D8Q004D3Q00014Q009C012Q000200022Q004D000100013Q00105D2Q0100024Q000B012Q00013Q00013Q000B3Q00030C3Q0057616974466F724368696C6403073Q004D6F64756C6573026Q0044402Q033Q004E657403063Q006D6F64756C6503073Q00726571756972652Q033Q0072656703113Q0052452F5265676973746572412Q7461636B2Q033Q00686974030E3Q0052452F526567697374657248697403063Q00612Q7365727400254Q0042016Q00206Q000100122Q000200023Q00122Q000300038Q0003000200062Q0001000B00013Q00040F012Q000B000100208D00013Q0001001216000300043Q001216000400034Q00FC0001000400022Q004D000200013Q001288010300064Q0046010400014Q009C01030002000200105D0102000500032Q004D000200013Q00208D000300010001001216000500083Q001216000600034Q00FC00030006000200105D0102000700032Q004D000200013Q00208D0003000100010012160005000A3Q001216000600034Q00FC00030006000200105D0102000900030012880102000B4Q004D000300013Q0020E300030003000700069A0103002300013Q00040F012Q002300012Q004D000300013Q0020E30003000300092Q00330002000200012Q000B012Q00017Q00043Q0003023Q006F7303053Q00636C6F636B026Q00084003053Q007063612Q6C00184Q004D7Q000657012Q000A0001000100040F012Q000A0001001288012Q00013Q00201F5Q00026Q000100024Q000100019Q00000100264Q000C0001000300040F012Q000C00012Q004D8Q00DA3Q00023Q001288012Q00013Q0020E35Q00022Q0065012Q000100022Q00B83Q00013Q001288012Q00043Q0006B700013Q000100022Q004D3Q00024Q004D8Q00333Q000200012Q004D8Q00DA3Q00024Q000B012Q00013Q00013Q000B3Q00030E3Q0046696E6446697273744368696C64030D3Q00506C6179657253637269707473030F3Q00436F6D6261744672616D65776F726B03073Q007265717569726503043Q007479706503053Q007461626C6503103Q00616374697665436F6E74726F2Q6C657200030B3Q00676574757076616C75657303053Q006465627567027Q004000294Q00F87Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q00040F012Q0009000100208D00013Q0001001216000300034Q00FC0001000300020006572Q01000C0001000100040F012Q000C00012Q000B012Q00013Q001288010200044Q0046010300014Q009C010200020002001288010300054Q0046010400024Q009C010300020002002681010300190001000600040F012Q001900010020E300030002000700267B000300190001000800040F012Q001900012Q00B8000200014Q000B012Q00013Q001288010300093Q000657010300210001000100040F012Q002100010012880103000A3Q00069A0103002100013Q00040F012Q002100010012880103000A3Q0020E300030003000900069A0103002800013Q00040F012Q002800012Q0046010400034Q0046010500024Q009C0104000200020020E300040004000B2Q00B8000400014Q000B012Q00017Q00023Q0003103Q00616374697665436F6E74726F2Q6C657203053Q007063612Q6C000E4Q004D8Q0065012Q000100020006210001000500013Q00040F012Q000500010020E300013Q00010006572Q0100080001000100040F012Q000800012Q000B012Q00013Q001288010200023Q0006B700033Q000100022Q0046012Q00014Q004D3Q00014Q00330002000200012Q000B012Q00013Q00013Q000A3Q00030F3Q00686974626F784D61676E697475646503043Q006D6174682Q033Q006D6178026Q004E4003093Q006D2Q6F6E52616E676503103Q0074696D65546F4E657874412Q7461636B028Q0003093Q00612Q7461636B696E67010003063Q00612Q7461636B00104Q005C7Q00122Q000100023Q00202Q00010001000300122Q000200046Q000300013Q00202Q0003000300054Q00010003000200104Q000100019Q0000304Q000600079Q0000304Q000800099Q0000206Q000A6Q000200016Q00017Q00143Q0003093Q0043686172616374657203063Q00737472696E6703053Q006C6F77657203043Q004E616D6503043Q0066696E6403063Q00736861646F77026Q00F03F03063Q0073752Q6D6F6E03063Q0069706169727303053Q004F776E657203073Q004F776E65724964030B3Q004F776E657255736572496403093Q004F776E65724E616D6503063Q004D617374657203083Q0053752Q6D6F6E6572030A3Q0053752Q6D6F6E65644279030C3Q00476574412Q7472696275746500034Q00028Q0001414Q004D00015Q0020E30001000100010006273Q00060001000100040F012Q000600012Q00E7000100014Q00DA000100023Q0012882Q0100023Q0020E30001000100030020E300023Q00042Q009C2Q0100020002001288010200023Q0020E30002000200032Q004D00035Q0020E30003000300042Q009C0102000200020006AD000100230001000200040F012Q00230001001288010200023Q00207C0002000200054Q000300013Q00122Q000400063Q00122Q000500076Q000600016Q00020006000200062Q000200230001000100040F012Q00230001001288010200023Q0020A60002000200054Q000300013Q00122Q000400083Q00122Q000500076Q000600016Q00020006000200062Q0002002500013Q00040F012Q002500012Q00E7000200014Q00DA000200023Q001288010200094Q0013010300073Q0012160004000A3Q0012160005000B3Q0012160006000C3Q00121C0007000D3Q00122Q0008000E3Q00122Q0009000F3Q00122Q000A00106Q0003000700012Q00B200020002000400040F012Q003C000100208D00073Q00112Q0046010900064Q00FC00070009000200267B0007003C0001001200040F012Q003C000100267B0007003C0001001300040F012Q003C000100267B0007003C0001001400040F012Q003C00012Q00E7000800014Q00DA000800023Q00062B000200310001000200040F012Q003100012Q00E700026Q00DA000200024Q000B012Q00017Q00173Q0003063Q0069706169727303073Q00456E656D696573030A3Q004368617261637465727303093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C030C3Q00476574412Q7472696275746503063Q004973426F617403163Q00476574506C6179657246726F6D4368617261637465720003153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403103Q0048756D616E6F6964522Q6F745061727403063Q004865616C7468028Q0003083Q00506F736974696F6E03093Q004D61676E697475646503093Q006D2Q6F6E52616E6765026Q00F03F03053Q007461626C6503043Q00736F727401554Q007C2Q015Q00122Q000200016Q000300023Q00122Q000400023Q00122Q000500036Q0003000200012Q00B200020002000400040F012Q004C0001001288010700043Q00208D0007000700052Q0046010900064Q00FC00070009000200069A0107004C00013Q00040F012Q004C0001001288010800013Q00208D0009000700062Q00DE0009000A4Q003501083Q000A00040F012Q004A000100208D000D000C0007001216000F00084Q00FC000D000F000200069A010D004A00013Q00040F012Q004A00012Q004D000D6Q0046010E000C4Q009C010D00020002000657010D004A0001000100040F012Q004A000100208D000D000C0009001216000F000A4Q00FC000D000F0002000657010D004A0001000100040F012Q004A00012Q004D000D00014Q0046010E000C4Q009C010D0002000200069A010D004A00013Q00040F012Q004A00012Q004D000D00023Q00208D000D000D000B2Q0046010F000C4Q00FC000D000F0002002681010D004A0001000C00040F012Q004A000100208D000D000C000D0012BB000F000E6Q000D000F000200202Q000E000C000500122Q0010000F6Q000E0010000200062Q000D004A00013Q00040F012Q004A000100069A010E004A00013Q00040F012Q004A00010020E3000F000D0010000ED30011004A0001000F00040F012Q004A00010020E3000F000E00120020E300103Q00122Q0032010F000F00100020E3000F000F00132Q004D001000033Q0020E30010001000140006F2000F004A0001001000040F012Q004A00012Q00D0001000013Q0020EF0010001000154Q001100036Q0012000C6Q0013000E6Q0014000F6Q0011000300012Q009E00010010001100062B000800130001000200040F012Q0013000100062B000200080001000200040F012Q00080001001288010200163Q0020E30002000200172Q0046010300013Q00028500046Q00EE0002000400012Q00DA000100024Q000B012Q00013Q00013Q00013Q00026Q00084002083Q0020E300023Q00010020E3000300010001000639010200050001000300040F012Q000500012Q001101026Q00E7000200014Q00DA000200024Q000B012Q00017Q00083Q0003053Q00726561647903093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303043Q00542Q6F6C030C3Q00476574412Q74726962757465030A3Q00576561706F6E5479706503053Q004D656C2Q6503053Q0053776F7264001A4Q004D7Q0020E35Q0001000657012Q00060001000100040F012Q000600012Q00E78Q00DA3Q00024Q004D3Q00013Q0020E35Q00020006210001000D00013Q00040F012Q000D000100208D00013Q0003001216000300044Q00FC000100030002000621000200120001000100040F012Q0012000100208D000200010005001216000400064Q00FC00020004000200267B000200170001000700040F012Q0017000100267B000200170001000800040F012Q001700012Q001101036Q00E7000300014Q00DA000300024Q000B012Q00017Q00163Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F745061727403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q004865616C7468028Q00026Q00F03F03043Q006D6174682Q033Q006D696E030B3Q006D2Q6F6E5461726765747303043Q0048656164027Q004003083Q00746F737472696E6703063Q005573657249642Q033Q00737562026Q00104003093Q00636F726F7574696E6503073Q0072752Q6E696E67026Q002640026Q002E4003053Q007063612Q6C007C4Q004D8Q0065012Q00010002000657012Q00060001000100040F012Q000600012Q00E78Q00DA3Q00024Q004D3Q00013Q0020E35Q00010006210001000D00013Q00040F012Q000D000100208D00013Q0002001216000300034Q00FC0001000300020006210002001200013Q00040F012Q0012000100208D00023Q0004001216000400054Q00FC00020004000200069A2Q01001900013Q00040F012Q0019000100069A0102001900013Q00040F012Q001900010020E3000300020006000EA70107001B0001000300040F012Q001B00012Q00E700036Q00DA000300024Q004D000300024Q00610103000100012Q004D000300034Q0046010400014Q009C0103000200022Q00D0000400033Q002681010400250001000700040F012Q002500012Q00E7000400014Q00DA000400024Q001301046Q004B000500053Q00122Q000600083Q00122Q000700093Q00202Q00070007000A4Q000800036Q000900043Q00202Q00090009000B4Q00070009000200122Q000800083Q00042Q0006006000012Q0073000A000300090020E3000A000A000800208D000B000A00020012BB000D000C6Q000B000D000200202Q000C000A000200122Q000E00036Q000C000E000200062Q000B004100013Q00040F012Q004100012Q00D0000D00043Q0020D1000D000D00084Q000E00026Q000F000A6Q0010000B6Q000E000200012Q009E0004000D000E00069A010C004A00013Q00040F012Q004A00012Q00D0000D00043Q0020D1000D000D00084Q000E00026Q000F000A6Q0010000C6Q000E000200012Q009E0004000D000E000657010B00560001000100040F012Q00560001000657010C00560001000100040F012Q005600012Q00D0000D00043Q0020AC010D000D00082Q0013010E00024Q0046010F000A4Q00730010000300090020E300100010000D2Q0023010E000200012Q009E0004000D000E0006570105005F0001000100040F012Q005F000100208D000D000A0002001216000F000C4Q00FC000D000F000200068E0005005F0001000D00040F012Q005F00012Q0073000D000300090020E30005000D000D0004060106003000010012880106000E4Q004C000700013Q00202Q00070007000F4Q00060002000200202Q00060006001000122Q0008000D3Q00122Q000900116Q00060009000200122Q0007000E3Q00122Q000800123Q00202Q0008000800132Q0077010800014Q003001073Q000200202Q00070007001000122Q000900143Q00122Q000A00156Q0007000A00024Q00060006000700122Q000700163Q0006B700083Q000100042Q004D3Q00054Q0046012Q00054Q0046012Q00044Q0046012Q00064Q00330007000200012Q00E7000700014Q00DA000700024Q000B012Q00013Q00013Q00063Q0003063Q006D6F64756C65030B3Q0052656D6F74654576656E74030B3Q0052656769737465724869742Q033Q00726567030A3Q00466972655365727665722Q033Q0068697400134Q00BD7Q00206Q000100206Q000200122Q000200036Q000300018Q000300019Q0000206Q000400206Q00056Q000200019Q0000206Q000600206Q00054Q000200016Q000300026Q00048Q000500038Q000500016Q00017Q000C3Q0003043Q0066617374030A3Q006F72696F6E436C69636B03093Q0061746B4D6574686F6403043Q004D2Q6F6E2Q033Q00412Q6C03043Q004175746F03013Q006D026Q00F03F03023Q006F7303053Q00636C6F636B03083Q0061746B44656C617903053Q007063612Q6C00354Q004D7Q000657012Q00110001000100040F012Q001100012Q004D3Q00013Q0020E35Q000100069A012Q001100013Q00040F012Q001100012Q004D3Q00013Q0020E35Q0002000657012Q00110001000100040F012Q001100012Q004D3Q00023Q000657012Q00120001000100040F012Q001200012Q004D3Q00033Q000657012Q00120001000100040F012Q001200012Q000B012Q00014Q004D3Q00013Q0020E35Q000300267B3Q001F0001000400040F012Q001F000100267B3Q001F0001000500040F012Q001F0001002681012Q001E0001000600040F012Q001E00012Q004D000100043Q0020E300010001000700267B0001001F0001000800040F012Q001F00012Q00112Q016Q00E7000100013Q0006572Q0100230001000100040F012Q002300012Q000B012Q00013Q001288010200093Q0020E300020002000A2Q00650102000100022Q004D000300054Q00320102000200032Q004D000300013Q0020E300030003000B0006760102002D0001000300040F012Q002D00012Q000B012Q00013Q001288010200093Q00206100020002000A4Q0002000100024Q000200053Q00122Q0002000C6Q000300066Q0002000200016Q00017Q00073Q00030A3Q006F72696F6E436C69636B03043Q006D6174682Q033Q006D6178026Q00F03F03053Q00666C2Q6F72030A3Q006F72696F6E427572737403053Q007063612Q6C002F4Q004D7Q000657012Q000D0001000100040F012Q000D00012Q004D3Q00013Q0020E35Q000100069A012Q000D00013Q00040F012Q000D00012Q004D3Q00023Q000657012Q000E0001000100040F012Q000E00012Q004D3Q00033Q000657012Q000E0001000100040F012Q000E00012Q000B012Q00013Q001288012Q00023Q002024014Q000300122Q000100043Q00122Q000200023Q00202Q0002000200054Q000300013Q00202Q0003000300064Q000200039Q00000200122Q000100046Q00025Q001216000300043Q0004630001002E00012Q00E700055Q001288010600073Q0006B700073Q000100022Q0046012Q00054Q004D3Q00044Q00330006000200010006570105002C0001000100040F012Q002C0001001288010600074Q004D000700054Q00330006000200012Q004D000600063Q0006570106002C0001000100040F012Q002C0001001288010600074Q004D000700074Q00330006000200012Q000F00055Q0004062Q01001B00012Q000B012Q00013Q00018Q00044Q004D3Q00014Q0065012Q000100022Q00B88Q000B012Q00017Q00043Q0003043Q004D2Q6F6E03063Q0052656D6F746503023Q0043462Q033Q0043463202274Q004D00025Q00069A0102000900013Q00040F012Q0009000100267B3Q00090001000100040F012Q0009000100267B3Q00090001000200040F012Q000900012Q00E700026Q00DA000200023Q002681012Q000E0001000100040F012Q000E00012Q004D000200014Q0049010200014Q009101025Q002681012Q00140001000300040F012Q001400012Q004D000200024Q0049010200014Q009101025Q00040F012Q00200001002681012Q001A0001000400040F012Q001A00012Q004D000200034Q0049010200014Q009101025Q00040F012Q00200001002681012Q00200001000200040F012Q002000012Q004D000200044Q0046010300014Q0051010200034Q009101026Q004D000200054Q00610102000100012Q004D000200064Q00610102000100012Q00E7000200014Q00DA000200024Q000B012Q00017Q000A3Q0003043Q006661737403093Q0061746B4D6574686F6403043Q004175746F03013Q006D03043Q004D2Q6F6E027Q0040026Q00F03F2Q033Q00412Q6C03063Q0069706169727303023Q00434601514Q004D00015Q0020E30001000100010006572Q0100100001000100040F012Q001000012Q004D000100013Q00069A2Q01000B00013Q00040F012Q000B00012Q004D000100024Q004601026Q003300010002000100040F012Q000F00012Q004D000100034Q00612Q01000100012Q004D000100044Q00612Q01000100012Q000B012Q00014Q004D00015Q0020E30001000100020026812Q01003B0001000300040F012Q003B00012Q004D000200054Q004D000300063Q0020E30003000300042Q0073000200020003002681010200200001000500040F012Q002000012Q004D000200074Q0065010200010002000657010200200001000100040F012Q002000012Q004D000200063Q0030930002000400062Q00E700025Q00123C000300076Q000400056Q000400043Q00122Q000500073Q00042Q0003003A00012Q004D000700084Q004D000800054Q004D000900063Q0020E30009000900042Q00730008000800092Q004601096Q00FC0007000900022Q0046010200073Q00069A0102003100013Q00040F012Q0031000100040F012Q005000012Q004D000700064Q0019010800063Q00202Q0008000800044Q000900056Q000900096Q00080008000900202Q00080008000700102Q00070004000800040601030026000100040F012Q005000010026812Q0100480001000800040F012Q00480001001288010200094Q004D000300054Q00B200020002000400040F012Q004500012Q004D000700084Q0046010800064Q004601096Q00EE00070009000100062B000200410001000200040F012Q0041000100040F012Q005000012Q004D000200084Q004D000300094Q00730003000300010006570103004E0001000100040F012Q004E00010012160003000A4Q004601046Q00EE0002000400012Q000B012Q00017Q000C3Q0003093Q0061746B4D6574686F6403043Q004175746F03023Q00687003063Q006C617374487003073Q006C617374446D6703063Q004865616C746803023Q006F7303053Q00636C6F636B027Q004003013Q006D026Q00F03F03043Q006E65617201434Q004D00015Q0020E30001000100010026812Q0100060001000200040F012Q00060001000657012Q00070001000100040F012Q000700012Q000B012Q00014Q004D000100013Q0020E30001000100030006AD0001001700013Q00040F012Q001700012Q004D000100014Q00BC000200016Q000300016Q00045Q00202Q00053Q000600122Q000600073Q00202Q0006000600084Q00060001000200102Q00030005000600102Q00020004000500102Q0001000300042Q000B012Q00013Q0020E300013Q00062Q004D000200013Q0020E30002000200040006762Q0100210001000200040F012Q002100012Q004D000100013Q001288010200073Q0020E30002000200082Q006501020001000200105D2Q01000500022Q004D000100013Q0020E300023Q000600105D2Q01000400020012882Q0100073Q0020E30001000100082Q00652Q01000100022Q004D000200013Q0020E30002000200052Q00322Q0100010002000ED3000900420001000100040F012Q004200012Q004D000100014Q0019010200013Q00202Q00020002000A4Q000300026Q000300036Q00020002000300202Q00020002000B00102Q0001000A00022Q004D000100013Q001288010200073Q0020E30002000200082Q006501020001000200105D2Q01000500022Q004D000100013Q0020E300010001000A0026812Q0100420001000B00040F012Q004200012Q004D000100014Q004D000200013Q0020E300020002000C2Q00A7000200023Q00105D2Q01000C00022Q000B012Q00017Q00083Q0003093Q0061746B4D6574686F6403043Q004175746F03013Q006D03073Q0020286175746F2903083Q004D65746F646F3A2003043Q006E65617203113Q00207C20636F6C61646F206E6F20616C766F035Q001B4Q004D7Q0020E35Q0001002681012Q000C0001000200040F012Q000C00012Q004D3Q00014Q009B2Q0100023Q00202Q0001000100038Q000100122Q000100049Q00000100064Q000E0001000100040F012Q000E00012Q004D7Q0020E35Q0001001216000100054Q004601026Q004D000300023Q0020E300030003000600069A0103001700013Q00040F012Q00170001001216000300073Q000657010300180001000100040F012Q00180001001216000300084Q00870001000100032Q00DA000100024Q000B012Q00017Q00053Q0003083Q006661726D4469737403043Q006E65617203043Q006D6174682Q033Q006D696E026Q00104001103Q000657012Q00040001000100040F012Q000400012Q004D00015Q0020E33Q000100012Q004D000100013Q0020E300010001000200069A2Q01000E00013Q00040F012Q000E00010012882Q0100033Q00205E0001000100044Q00025Q00122Q000300056Q0001000300026Q00014Q00DA3Q00024Q000B012Q00017Q00093Q0003093Q00776F726B7370616365030D3Q0043752Q72656E7443616D65726103063Q0061696D43616D03063Q00434672616D6503063Q006C2Q6F6B417403083Q00506F736974696F6E03143Q00576F726C64546F56696577706F7274506F696E74030B3Q00476574477569496E73657403053Q007063612Q6C01243Q0012882Q0100013Q0020E30001000100020006572Q0100050001000100040F012Q000500012Q000B012Q00014Q004D00025Q0020E300020002000300069A0102001000013Q00040F012Q00100001001288010200043Q0020E30002000200050020E30003000100040020E30003000300062Q004601046Q00FC00020004000200105D2Q01000400022Q004D000200013Q000657010200140001000100040F012Q001400012Q000B012Q00013Q00208D0002000100072Q004601046Q007600020004000300069A0103002300013Q00040F012Q002300012Q004D000400023Q00208D0004000400082Q009C010400020002001288010500093Q0006B700063Q000100032Q004D3Q00014Q0046012Q00024Q0046012Q00044Q00330005000200012Q000F00046Q000B012Q00013Q00013Q00043Q0003123Q0053656E644D6F7573654D6F76654576656E7403013Q005803013Q005903043Q0067616D65000C4Q00577Q00206Q00014Q000200013Q00202Q0002000200024Q000300013Q00202Q0003000300034Q000400023Q00202Q0004000400034Q00030003000400122Q000400048Q000400016Q00017Q00083Q0003063Q0069706169727303043Q00456E756D03073Q004B6579436F646503013Q005A03013Q005803013Q004303013Q005603053Q007063612Q6C01234Q004D00015Q0006572Q0100040001000100040F012Q000400012Q000B012Q00013Q00069A012Q000900013Q00040F012Q000900012Q004D000100014Q004601026Q00330001000200010012882Q0100014Q0013010200043Q001288010300023Q0020E30003000300030020E3000300030004001288010400023Q0020E30004000400030020E3000400040005001288010500023Q0020E30005000500030020E3000500050006001288010600023Q0020E30006000600030020E30006000600072Q00230102000400012Q00B200010002000300040F012Q00200001001288010600083Q0006B700073Q000100022Q004D8Q0046012Q00054Q00330006000200012Q000F00045Q00062B0001001A0001000200040F012Q001A00012Q000B012Q00013Q00013Q00053Q00030C3Q0053656E644B65794576656E7403043Q0067616D6503043Q007461736B03043Q0077616974029A5Q99A93F00134Q004D7Q00208D5Q00012Q00E7000200014Q004D000300014Q00E700045Q001288010500024Q00EE3Q00050001001288012Q00033Q0020E35Q0004001216000100054Q00333Q000200012Q004D7Q00208D5Q00012Q00E700026Q004D000300014Q00E700045Q001288010500024Q00EE3Q000500012Q000B012Q00019Q002Q0001054Q00722Q018Q00028Q000100026Q00019Q0000017Q00133Q0003063Q0069706169727303073Q00456E656D69657303093Q0053656142656173747303093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030B3Q004765744368696C6472656E03043Q004E616D6503063Q00737472696E6703043Q0066696E64026Q00F03F03153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q004865616C7468028Q0003053Q007461626C6503063Q00696E736572742Q033Q006D646C03043Q00706172742Q033Q0068756D02484Q001301025Q001288010300013Q00068E000400080001000100040F012Q000800012Q0013010400023Q001216000500023Q001216000600034Q00230104000200012Q00B200030002000500040F012Q00440001001288010800043Q00208D0008000800052Q0046010A00074Q00FC0008000A000200069A0108004400013Q00040F012Q00440001001288010900013Q00208D000A000800062Q00DE000A000B4Q003501093Q000B00040F012Q004200012Q004D000E5Q0020E3000F000D00072Q009C010E00020002001288010F00014Q004601106Q00B2000F0002001100040F012Q00400001001288011400083Q0020180114001400094Q0015000E6Q001600133Q00122Q0017000A6Q001800016Q00140018000200062Q0014004000013Q00040F012Q0040000100208D0014000D000B0012160016000C4Q00FC0014001600022Q00E7001500013Q00069A0114003000013Q00040F012Q003000010020E300160014000D000EA7010E002F0001001600040F012Q002F00012Q001101156Q00E7001500014Q004D001600014Q00460117000D4Q009C01160002000200069A0116004200013Q00040F012Q0042000100069A0115004200013Q00040F012Q004200010012880117000F3Q0020080117001700104Q001800026Q00193Q000300102Q00190011000D00102Q00190012001600102Q0019001300144Q00170019000100044Q0042000100062B000F001C0001000200040F012Q001C000100062B000900150001000200040F012Q0015000100062B0003000A0001000200040F012Q000A00012Q00DA000200024Q000B012Q00017Q00053Q0003063Q0069706169727303043Q007061727403083Q00506F736974696F6E03093Q004D61676E6974756465028Q00011E4Q00872Q018Q0001000100024Q000200033Q00122Q000400016Q00058Q00040002000600044Q0018000100069A2Q01001000013Q00040F012Q001000010020E30009000800020020E400090009000300202Q000A000100034Q00090009000A00202Q00090009000400062Q000900110001000100040F012Q00110001001216000900053Q00069A0103001500013Q00040F012Q00150001000676010900180001000300040F012Q001800012Q0046010A00084Q0046010300094Q00460102000A3Q00062B000400070001000200040F012Q000700012Q0046010400024Q0046010500034Q0036000400034Q000B012Q00017Q001A3Q0003043Q007061727403063Q00506172656E7403043Q006E65617203043Q006D6174682Q033Q006D696E026Q00144003083Q00506F736974696F6E03093Q004D61676E6974756465026Q004E4003063Q00434672616D652Q033Q006E657703023Q006F7303053Q00636C6F636B028Q002Q033Q006D646C026Q003E402Q033Q0068756D03063Q004865616C7468026Q00E03F03063Q00776561706F6E026Q00F83F03043Q007461736B03043Q0077616974030A3Q006F72696F6E436C69636B027B14AE47E17A843F03083Q0061746B44656C6179068B4Q004D00066Q006501060001000200069A0106000800013Q00040F012Q000800010020E300073Q00010020E3000700070002000657010700090001000100040F012Q000900012Q000B012Q00014Q0046010700024Q004D000800013Q0020E300080008000300069A0108001400013Q00040F012Q00140001001288010800043Q00205E0008000800054Q000900023Q00122Q000A00066Q0008000A00024Q000700083Q0006B700083Q000100032Q004D3Q00024Q0046017Q0046012Q00073Q0020E30009000600072Q0046010A00084Q0065010A000100022Q003201090009000A0020E3000900090008000ED30009002B0001000900040F012Q002B00012Q004D000900033Q001204010A000A3Q00202Q000A000A000B4Q000B00086Q000B00016Q000A3Q00024Q000B00046Q000C00016Q0009000C000200062Q0009002B0001000100040F012Q002B00012Q000B012Q00014Q004D000900044Q009B00090001000100122Q0009000C3Q00202Q00090009000D4Q00090001000200122Q000A000E3Q00122Q000B000C3Q00202Q000B000B000D4Q000B000100022Q0046010C00014Q0065010C0001000200069A010C008A00013Q00040F012Q008A00010020E3000C3Q000F0020E3000C000C000200069A010C008A00013Q00040F012Q008A00010020E3000C3Q00010020E3000C000C000200069A010C008A00013Q00040F012Q008A0001001288010C000C3Q0020E3000C000C000D2Q0065010C000100022Q0032010C000C000900068E000D00470001000500040F012Q00470001001216000D00103Q000676010C008A0001000D00040F012Q008A00010020E3000C3Q001100069A010C005100013Q00040F012Q005100010020E3000C3Q00110020E3000C000C00120026AB000C00510001000E00040F012Q0051000100040F012Q008A0001001288010C000C3Q0020E3000C000C000D2Q0065010C000100022Q0032010C000C000B000ED30013005F0001000C00040F012Q005F0001001288010C000C3Q002059010C000C000D4Q000C000100024Q000B000C6Q000C00056Q000D00063Q00202Q000D000D00144Q000C000200012Q004D000C00074Q0046010D00084Q0065010D000100020020E3000E3Q00010020E3000E000E00072Q00FC000C000E0002000657010C00680001000100040F012Q0068000100040F012Q008A00012Q004D000C00084Q00C3000C000100014Q000C00093Q00202Q000D3Q00114Q000C0002000100062Q0003007D00013Q00040F012Q007D0001001288010C000C3Q0020E3000C000C000D2Q0065010C000100022Q0032010C000C000A000ED30015007D0001000C00040F012Q007D0001001288010C000C3Q0020E3000C000C000D2Q0065010C000100022Q0046010A000C4Q004D000C000A3Q0020E3000D3Q00010020E3000D000D00072Q0033000C00020001001288010C00163Q0020E3000C000C00172Q004D000D00063Q0020E3000D000D001800069A010D008600013Q00040F012Q00860001001216000D00193Q000657010D00880001000100040F012Q008800012Q004D000D00063Q0020E3000D000D001A2Q0033000C0002000100040F012Q003400012Q000B012Q00013Q00013Q00023Q0003043Q007061727403083Q00506F736974696F6E00084Q004B019Q000100013Q00202Q00010001000100202Q0001000100024Q000200028Q00029Q008Q00017Q00093Q0003043Q004E616D65034Q0003153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F6964030B3Q00446973706C61794E616D6503063Q0069706169727303063Q00737472696E6703043Q0066696E64026Q00F03F022A4Q000D01025Q00202Q00033Q00014Q00020002000200122Q000300023Q00202Q00043Q000300122Q000600046Q00040006000200062Q0004000D00013Q00040F012Q000D00012Q004D00055Q0020E30006000400052Q009C0105000200022Q0046010300053Q001288010500064Q0046010600014Q00B200050002000700040F012Q00250001001288010A00073Q002053000A000A00084Q000B00026Q000C00093Q00122Q000D00096Q000E00016Q000A000E000200062Q000A00230001000100040F012Q00230001001288010A00073Q002018010A000A00084Q000B00036Q000C00093Q00122Q000D00096Q000E00016Q000A000E000200062Q000A002500013Q00040F012Q002500012Q00E7000A00014Q00DA000A00023Q00062B000500110001000200040F012Q001100012Q00E700056Q00DA000500024Q000B012Q00017Q00153Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403043Q004E50437303063Q00697061697273030B3Q004765744368696C6472656E03053Q007461626C6503063Q00636F6E63617403013Q007C03023Q006F7303053Q00636C6F636B03013Q0074026Q00244003043Q0070617274028Q00030E3Q0047657444657363656E64616E7473026Q00F03F025Q0040AF4003043Q007461736B03043Q00776169742Q033Q0049734103053Q004D6F64656C01694Q004D00016Q00652Q01000100022Q0062000200033Q0006B700043Q000100062Q004D3Q00014Q0046017Q004D3Q00024Q0046012Q00014Q0046012Q00034Q0046012Q00023Q001289000500013Q00202Q00050005000200122Q000700036Q00050007000200062Q0005001A00013Q00040F012Q001A0001001288010600043Q00208D0007000500052Q00DE000700084Q003501063Q000800040F012Q001800012Q0046010B00044Q0046010C000A4Q0033000B0002000100062B000600150001000200040F012Q00150001000657010200270001000100040F012Q00270001001288010600043Q001288010700013Q00208D0007000700052Q00DE000700084Q003501063Q000800040F012Q002500012Q0046010B00044Q0046010C000A4Q0033000B0002000100062B000600220001000200040F012Q0022000100069A0102002A00013Q00040F012Q002A00012Q00DA000200023Q001288010600063Q0020840106000600074Q00075Q00122Q000800086Q0006000800024Q000700036Q00070007000600062Q0007003C00013Q00040F012Q003C0001001288010800093Q0020E300080008000A2Q00650108000100020020E300090007000B2Q00320108000800090026950008003C0001000C00040F012Q003C00010020E300080007000D2Q00DA000800024Q0062000800083Q0012590009000E3Q00122Q000A00043Q00122Q000B00013Q00202Q000B000B000F4Q000B000C6Q000A3Q000C00044Q005D00010020AC0109000900100020F6000F00090011002681010F004B0001000E00040F012Q004B0001001288010F00123Q0020E3000F000F00132Q0061010F0001000100208D000F000E0014001216001100154Q00FC000F0011000200069A010F005D00013Q00040F012Q005D00012Q004D000F00014Q00460110000E4Q004601116Q00FC000F0011000200069A010F005D00013Q00040F012Q005D00012Q004D000F00024Q00460110000E4Q009C010F0002000200069A010F005D00013Q00040F012Q005D00012Q00460108000F3Q00040F012Q005F000100062B000A00440001000200040F012Q004400012Q004D000A00034Q0013010B3Q0002001288010C00093Q0020E3000C000C000A2Q0065010C0001000200105D010B000B000C00105D010B000D00082Q009E000A0006000B2Q00DA000800024Q000B012Q00013Q00013Q00053Q002Q033Q0049734103053Q004D6F64656C03083Q00506F736974696F6E03093Q004D61676E6974756465028Q0001253Q00208D00013Q0001001216000300024Q00FC00010003000200069A2Q01002400013Q00040F012Q002400012Q004D00016Q004601026Q004D000300014Q00FC00010003000200069A2Q01002400013Q00040F012Q002400012Q004D000100024Q004601026Q009C2Q010002000200069A2Q01002400013Q00040F012Q002400012Q004D000200033Q00069A0102001A00013Q00040F012Q001A00010020E30002000100032Q004D000300033Q0020E30003000300032Q00320102000200030020E30002000200040006570102001B0001000100040F012Q001B0001001216000200054Q004D000300043Q00069A0103002100013Q00040F012Q002100012Q004D000300043Q000676010200240001000300040F012Q002400012Q0046010300014Q00B8000200044Q00B8000300054Q000B012Q00017Q00273Q00026Q00F03F026Q00444003083Q00506F736974696F6E03093Q004D61676E6974756465026Q00344003093Q00696E646F206174652003023Q00202803043Q006D61746803053Q00666C2Q6F7203023Q006D2903063Q00434672616D652Q033Q006E657703073Q00566563746F7233028Q00026Q000840026Q001040030A3Q0074772Q656E53702Q6564026Q00394003063Q00697061697273030A3Q006E616F20616368656920031D3Q002028766120617465206120696C68612064656C6520756D612076657A2903043Q007461736B03043Q0077616974027Q0040025Q00407F4003143Q00696E646F2070617261206120696C6861206465202Q033Q006D696E025Q00E0854003043Q00556E697403013Q005803013Q0059025Q0080514003013Q005A030B3Q0070726F637572616E646F202Q033Q003Q2E02CD5QCCF43F2Q033Q00636F73026Q005E402Q033Q0073696E05AE3Q001216000500013Q001216000600023Q001216000700013Q000463000500AB00012Q0046010900024Q00650109000100020006570109000A0001000100040F012Q000A00012Q0062000900094Q00DA000900024Q004D00096Q0065010900010002000657010900100001000100040F012Q001000012Q0062000A000A4Q00DA000A00024Q004D000A00014Q0046010B6Q009C010A0002000200069A010A004300013Q00040F012Q004300010020E3000B000900030020E3000C000A00032Q0032010B000B000C0020E3000B000B0004000ED3000500360001000B00040F012Q003600012Q0046010C00033Q0012D6000D00066Q000E00043Q00122Q000F00073Q00122Q001000083Q00202Q0010001000094Q0011000B6Q00100002000200122Q0011000A6Q000D000D00114Q000C000200012Q004D000C00023Q001288010D000B3Q0020E3000D000D000C0020E3000E000A0003001203000F000D3Q00202Q000F000F000C00122Q0010000E3Q00122Q0011000F3Q00122Q001200106Q000F001200024Q000E000E000F4Q000D000200024Q000E00033Q00202Q000E000E00112Q0046010F00024Q00EE000C000F00012Q004D000C6Q0065010C000100022Q00460109000C3Q00069A010900AA00013Q00040F012Q00AA00010020E3000C000900030020E3000D000A00032Q0032010C000C000D0020E3000C000C0004002695000C00AA0001001200040F012Q00AA00012Q00DA000A00023Q00040F012Q00AA00012Q0062000B000B3Q001288010C00133Q00068E000D00480001000100040F012Q004800012Q0013010D6Q00B2000C0002000E00040F012Q00500001000657010B00500001000100040F012Q005000012Q004D001100044Q0046011200104Q009C0111000200022Q0046010B00113Q00062B000C004A0001000200040F012Q004A0001000657010B00600001000100040F012Q006000012Q0046010C00033Q001245000D00146Q000E00043Q00122Q000F00156Q000D000D000F4Q000C0002000100122Q000C00163Q00202Q000C000C001700122Q000D00186Q000C000200014Q000C000C4Q00DA000C00023Q0020E3000C000900032Q0032010C000C000B0020E3000C000C0004000ED3001900880001000C00040F012Q008800012Q0046010D00033Q0012D6000E001A6Q000F00043Q00122Q001000073Q00122Q001100083Q00202Q0011001100094Q0012000C6Q00110002000200122Q0012000A6Q000E000E00124Q000D000200010020E3000D000900032Q0032010D000B000D001288010E00083Q0020E3000E000E001B0020E3000F000D00040012160010001C4Q00FC000E001000020020E3000F000900030020E30010000D001D2Q006000100010000E2Q0033010F000F00102Q004D001000023Q0012880111000B3Q0020E300110011000C0020E30012000F001E0020E30013000B001F0020AC0113001300200020E30014000F00212Q00FC0011001400022Q004D001200033Q0020E30012001200112Q0046011300024Q00EE00100013000100040F012Q00AA00012Q0046010D00033Q001216000E00224Q0046010F00043Q001216001000234Q0087000E000E00102Q0033000D000200010020AF010D000800242Q004D000E00023Q001288010F000B3Q0020E3000F000F000C0012880110000D3Q0020E300100010000C001288011100083Q0020E30011001100252Q00460112000D4Q009C0111000200020020AF011100110026001216001200023Q001288011300083Q0020E30013001300272Q00460114000D4Q009C0113000200020020AF0113001300262Q00FC0010001300022Q00330110000B00102Q009C010F000200022Q004D001000033Q0020E30010001000112Q0046011100024Q00EE000E00110001001288010E00163Q0020E3000E000E0017001216000F00014Q0033000E000200010004060105000400012Q0062000500054Q00DA000500024Q000B012Q00017Q000A3Q00028Q0003063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030F3Q0050726F78696D69747950726F6D707403133Q006669726570726F78696D69747970726F6D707403053Q007063612Q6C026Q00F03F030D3Q00436C69636B4465746563746F7203113Q0066697265636C69636B6465746563746F72012D3Q001216000100013Q000657012Q00040001000100040F012Q000400012Q00DA000100023Q001288010200023Q00208D00033Q00032Q00DE000300044Q003501023Q000400040F012Q0029000100208D000700060004001216000900054Q00FC00070009000200069A0107001B00013Q00040F012Q001B0001001288010700063Q00069A0107001B00013Q00040F012Q001B0001001288010700073Q0006B700083Q000100012Q0046012Q00064Q00D500070002000100122Q000700073Q00122Q000800066Q000900066Q00070009000100202Q00010001000800044Q0028000100208D000700060004001216000900094Q00FC00070009000200069A0107002800013Q00040F012Q002800010012880107000A3Q00069A0107002800013Q00040F012Q00280001001288010700073Q0012880108000A4Q0046010900064Q00EE0007000900010020AC2Q01000100082Q000F00055Q00062B000200090001000200040F012Q000900012Q00DA000100024Q000B012Q00013Q00013Q00023Q00030C3Q00486F6C644475726174696F6E029Q00034Q004D7Q0030933Q000100022Q000B012Q00017Q00063Q0003053Q007063612Q6C034Q002Q033Q0073796E03073Q0072657175657374030C3Q00682Q74705F7265717565737403043Q00426F647901293Q0012882Q0100013Q0006B700023Q000100012Q0046017Q00B200010002000200069A2Q01000B00013Q00040F012Q000B000100069A0102000B00013Q00040F012Q000B000100267B0002000B0001000200040F012Q000B00012Q00DA000200023Q001288010300033Q00069A0103001200013Q00040F012Q00120001001288010300033Q0020E3000300030004000657010300160001000100040F012Q00160001001288010300043Q000657010300160001000100040F012Q00160001001288010300053Q00069A0103002600013Q00040F012Q00260001001288010400013Q0006B700050001000100022Q0046012Q00034Q0046017Q00B200040002000500069A0104002600013Q00040F012Q0026000100069A0105002600013Q00040F012Q002600010020E300060005000600069A0106002600013Q00040F012Q002600010020E30006000500062Q00DA000600024Q0062000400044Q00DA000400024Q000B012Q00013Q00023Q00023Q0003043Q0067616D6503073Q00482Q747047657400063Q001288012Q00013Q00208D5Q00022Q004D00026Q0051012Q00024Q0091017Q000B012Q00017Q00033Q002Q033Q0055726C03063Q004D6574686F642Q033Q0047455400084Q004D8Q00132Q013Q00022Q004D000200013Q00105D2Q01000100020030930001000200032Q0051012Q00014Q0091017Q000B012Q00019Q003Q00054Q00FD9Q009Q003Q00018Q00018Q00017Q00063Q0003043Q007461736B03053Q0064656C6179026Q00444003053Q007063612Q6C030D3Q00652Q726F206E6F20686F703A2003083Q00746F737472696E6701224Q004D00015Q00069A2Q01000400013Q00040F012Q000400012Q000B012Q00014Q00E7000100014Q00B800015Q0012882Q0100013Q0020E3000100010002001216000200033Q0006B700033Q000100012Q004D8Q00EE0001000300010012882Q0100043Q0006B700020001000100072Q0046017Q004D3Q00014Q004D3Q00024Q004D3Q00034Q004D3Q00044Q004D3Q00054Q004D3Q00064Q00B20001000200020006572Q0100210001000100040F012Q002100012Q00E700036Q008301038Q00035Q00122Q000400053Q00122Q000500066Q000600026Q0005000200024Q0004000400054Q0003000200012Q000B012Q00013Q00028Q00034Q00E78Q00B88Q000B012Q00017Q00263Q00031C3Q0070726F637572616E646F206F7574726F207365727669646F723Q2E034Q00026Q00F03F026Q00084003223Q00682Q7470733A2Q2F67616D65732E726F626C6F782E636F6D2F76312F67616D65732F03043Q0067616D6503073Q00506C616365496403283Q002F736572766572732F5075626C69633F736F72744F726465723D44657363266C696D69743D312Q3003083Q0026637572736F723D030A3Q004A534F4E4465636F646503063Q0069706169727303043Q006461746103023Q00696403053Q004A6F62496403073Q00706C6179696E67030A3Q006D6178506C6179657273027Q004003053Q007461626C6503063Q00696E73657274030E3Q006E65787450616765437572736F72026Q00244003053Q007063612Q6C028Q00026Q00104003043Q006D61746803063Q0072616E646F6D031A3Q00696E646F2070617261206F7574726F207365727669646F72202803063Q002F34293Q2E03023Q006F7303053Q00636C6F636B026Q001C4003043Q007461736B03043Q0077616974026Q33D33F2Q01026Q00F83F03433Q006F206A6F676F2072656375736F75206F73207365727669646F7265732028652Q726F202Q3733293B207573616E646F2074656C65706F72746520616C6561746F72696F03083Q0054656C65706F727400954Q004D7Q001216000100014Q00333Q000200012Q0013016Q001216000100023Q001216000200033Q001216000300043Q001216000400033Q0004630002004C0001001216000600053Q001288010700063Q0020E3000700070007001216000800084Q008700060006000800267B000100140001000200040F012Q001400012Q0046010700063Q001216000800094Q0046010900014Q00870006000700092Q004D000700014Q0046010800064Q009C0107000200020006570107001A0001000100040F012Q001A000100040F012Q004C00012Q004D000800023Q00208D00080008000A2Q0046010A00074Q00FC0008000A00020012880109000B3Q0020E3000A0008000C000657010A00230001000100040F012Q002300012Q0013010A6Q00B200090002000B00040F012Q003F00010020E3000E000D000D001288010F00063Q0020E3000F000F000E0006AD000E003F0001000F00040F012Q003F00012Q004D000E00033Q0020E3000F000D000D2Q0073000E000E000F000657010E003F0001000100040F012Q003F00010020E3000E000D000F00069A010E003F00013Q00040F012Q003F00010020E3000E000D001000069A010E003F00013Q00040F012Q003F00010020E3000E000D000F0020E3000F000D0010002078000F000F0011000676010E003F0001000F00040F012Q003F0001001288010E00123Q0020E3000E000E00132Q0046010F5Q0020E30010000D000D2Q00EE000E0010000100062B000900250001000200040F012Q002500010020E300090008001400068E000100450001000900040F012Q00450001001216000100024Q00D000095Q000E6C0015004C0001000900040F012Q004C00010026812Q01004B0001000200040F012Q004B000100040F012Q004C0001000406010200090001001288010200163Q00028500036Q00330002000200012Q00D000025Q000ED30017008B0001000200040F012Q008B0001001216000200033Q001216000300183Q001216000400033Q0004630002008B0001001288010600193Q00201B00060006001A00122Q000700036Q00088Q0006000800024Q00063Q00064Q00078Q000700046Q00075Q00122Q0008001B6Q000900053Q001216000A001C4Q008700080008000A2Q0033000700020001001288010700163Q0006B700080001000100032Q004D3Q00054Q0046012Q00064Q004D3Q00064Q009C0107000200020012880108001D3Q0020E300080008001E2Q006501080001000200069A0107007D00013Q00040F012Q007D00012Q004D000900043Q0006570109007D0001000100040F012Q007D00010012880109001D3Q0020E300090009001E2Q00650109000100022Q00320109000900080026950009007D0001001F00040F012Q007D0001001288010900203Q0020E3000900090021001216000A00224Q003300090002000100040F012Q006D000100069A0107008300013Q00040F012Q008300012Q004D000900043Q000657010900830001000100040F012Q008300012Q000B012Q00014Q004D000900033Q00208C00090006002300122Q000900203Q00202Q00090009002100122Q000A00246Q0009000200014Q00065Q0004060102005600012Q004D00025Q001216000300254Q00330002000200012Q004D000200053Q00208D000200020026001288010400063Q0020E30004000400072Q004D000500064Q00EE0002000500012Q000B012Q00013Q00023Q00043Q0003113Q0071756575655F6F6E5F74656C65706F727403063Q00697366696C65030C3Q004F72696F6E4875622E6C756103263Q006C6F6164737472696E67287265616466696C6528224F72696F6E4875622E6C7561222Q292829000F3Q001288012Q00013Q00069A012Q000E00013Q00040F012Q000E0001001288012Q00023Q00069A012Q000E00013Q00040F012Q000E0001001288012Q00023Q001216000100034Q009C012Q0002000200069A012Q000E00013Q00040F012Q000E0001001288012Q00013Q001216000100044Q00333Q000200012Q000B012Q00017Q00033Q0003173Q0054656C65706F7274546F506C616365496E7374616E636503043Q0067616D6503073Q00506C616365496400084Q004D7Q00208D5Q0001001288010200023Q0020E30002000200032Q004D000300014Q004D000400024Q00EE3Q000400012Q000B012Q00017Q00093Q0003053Q007461626C6503063Q00696E7365727403043Q006C6973742Q033Q006B657903043Q007072696F2Q033Q006861732Q033Q0072756E03023Q00656E03043Q00736F727405123Q001288010500013Q0020E30005000500022Q004D00065Q0020E30006000600032Q001301073Q000500105D010700043Q00105D01070005000100105D01070006000200105D01070007000300105D0107000800042Q00EE000500070001001288010500013Q0020E30005000500092Q004D00065Q0020E300060006000300028500076Q00EE0005000700012Q000B012Q00013Q00013Q00013Q0003043Q007072696F02083Q0020E300023Q00010020E3000300010001000639010200050001000300040F012Q000500012Q001101026Q00E7000200014Q00DA000200024Q000B012Q00017Q00033Q0003023Q00656E2Q033Q006B65793Q010F3Q0020E300013Q000100069A2Q01000600013Q00040F012Q000600010020E300013Q00012Q00492Q0100014Q00912Q016Q004D00015Q0020E300023Q00022Q007300010001000200267B0001000C0001000300040F012Q000C00012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00053Q0003063Q0069706169727303043Q006C69737403043Q007072696F03053Q007063612Q6C2Q033Q00686173011C3Q0012152Q0100016Q00025Q00202Q0002000200024Q00010002000300044Q001700010020E30006000500030006F23Q00090001000600040F012Q0009000100040F012Q001900012Q004D000600014Q0046010700054Q009C01060002000200069A0106001700013Q00040F012Q00170001001288010600043Q0020E30007000500052Q00B200060002000700069A0106001700013Q00040F012Q0017000100069A0107001700013Q00040F012Q001700012Q00E7000800014Q00DA000800023Q00062B000100050001000200040F012Q000500012Q00E700016Q00DA000100024Q000B012Q00017Q00023Q0003043Q007461736B03053Q00737061776E000D3Q001288012Q00013Q0020E35Q00020006B700013Q000100082Q004D8Q004D3Q00014Q004D3Q00024Q004D3Q00034Q004D3Q00044Q004D3Q00054Q004D3Q00064Q004D3Q00074Q00333Q000200012Q000B012Q00013Q00013Q00113Q0003063Q00506172656E7403063Q0069706169727303043Q006C69737403053Q007761734F6E2Q033Q006B657903083Q00636C65616E75707303053Q007063612Q6C2Q033Q00686173028Q002Q033Q0072756E03063Q00652Q726F3A2003083Q00746F737472696E6703043Q007461736B03043Q0077616974026Q00F83F029A5Q99D93F02B81E85EB51B89E3F00754Q004D7Q000657012Q00720001000100040F012Q007200012Q004D3Q00013Q0020E35Q000100069A012Q007200013Q00040F012Q00720001001288012Q00024Q004D000100023Q0020E30001000100032Q00B23Q0002000200040F012Q002800012Q004D000500034Q0046010600044Q009C0105000200022Q004D000600023Q0020E30006000600040020E30007000400052Q007300060006000700069A0106002400013Q00040F012Q00240001000657010500240001000100040F012Q002400012Q0062000600064Q00B8000600043Q001215010600026Q000700023Q00202Q0007000700064Q00060002000800044Q00220001001288010B00074Q0046010C000A3Q0020E3000D000400052Q00EE000B000D000100062B0006001E0001000200040F012Q001E00012Q004D000600023Q0020E30006000600040020E30007000400052Q009E00060007000500062B3Q000C0001000200040F012Q000C00012Q00627Q0012152Q0100026Q000200023Q00202Q0002000200034Q00010002000300044Q003E00012Q004D000600034Q0046010700054Q009C01060002000200069A0106003E00013Q00040F012Q003E0001001288010600073Q0020E30007000500082Q00B200060002000700069A0106003E00013Q00040F012Q003E000100069A0107003E00013Q00040F012Q003E00012Q0046012Q00053Q00040F012Q0040000100062B000100300001000200040F012Q0030000100069A012Q006600013Q00040F012Q006600012Q00E7000100014Q00B8000100053Q001216000100094Q00E700025Q0006B700033Q000100062Q004D8Q004D3Q00034Q0046017Q0046012Q00014Q0046012Q00024Q004D3Q00063Q001288010400073Q0020E300053Q000A2Q0046010600033Q0006B700070001000100022Q004D3Q00074Q0046017Q0076000400070005000657010400640001000100040F012Q006400012Q0062000600064Q00B8000600044Q004D000600073Q0020E300073Q00050012160008000B3Q0012880109000C4Q0046010A00054Q009C0109000200022Q00870008000800092Q00EE0006000800010012880106000D3Q0020E300060006000E0012160007000F4Q00330006000200012Q000F00015Q00040F012Q006C00012Q00E700016Q00292Q0100053Q00122Q0001000D3Q00202Q00010001000E00122Q000200106Q0001000200010012882Q01000D3Q00208300010001000E00122Q000200116Q0001000200019Q0000046Q00012Q00E78Q00B83Q00054Q000B012Q00013Q00023Q00043Q0003023Q006F7303053Q00636C6F636B026Q33D33F03043Q007072696F001E4Q004D7Q000657012Q00080001000100040F012Q000800012Q004D3Q00014Q004D000100024Q009C012Q00020002000657012Q000A0001000100040F012Q000A00012Q00E78Q00DA3Q00023Q001288012Q00013Q0020505Q00026Q000100024Q000100039Q000001000E2Q0003001A00013Q00040F012Q001A0001001288012Q00013Q0020E35Q00022Q0065012Q000100022Q00B83Q00034Q004D3Q00054Q004D000100023Q0020E30001000100042Q009C012Q000200022Q00B83Q00044Q004D3Q00044Q00A78Q00DA3Q00024Q000B012Q00017Q00013Q002Q033Q006B657901064Q00982Q018Q000200013Q00202Q0002000200014Q00038Q0001000300016Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403093Q00506C6179657247756903043Q004D61696E000B4Q00F87Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q00040F012Q0009000100208D00013Q0001001216000300034Q00FC0001000300022Q00DA000100024Q000B012Q00017Q00043Q002Q033Q0049734103093Q004775694F626A65637403073Q0056697369626C6503063Q00506172656E7402144Q004601025Q00069A0102001100013Q00040F012Q001100010006AD000200110001000100040F012Q0011000100208D000300020001001216000500024Q00FC00030005000200069A0103000F00013Q00040F012Q000F00010020E30003000200030006570103000F0001000100040F012Q000F00012Q00E700036Q00DA000300023Q0020E300020002000400040F012Q000100012Q00E7000300014Q00DA000300024Q000B012Q00017Q00063Q0003063Q00737472696E6703043Q0067737562034Q00030C3Q005E25732A282E2D2925732A2403023Q00253103053Q006C6F776572010E3Q0012882Q0100013Q0020E300010001000200068E0002000500013Q00040F012Q00050001001216000200033Q001216000300043Q0012C0000400056Q00010004000200122Q000200013Q00202Q0002000200064Q000300016Q000200036Q00029Q0000017Q000A3Q0003183Q0046696E644669727374416E636573746F724F66436C612Q7303093Q005363722Q656E477569028Q00030E3Q0049676E6F7265477569496E73657403053Q007063612Q6C03013Q005903103Q004162736F6C757465506F736974696F6E03013Q0058030C3Q004162736F6C75746553697A65027Q004001213Q00208F00013Q000100122Q000300026Q00010003000200122Q000200033Q00062Q0001000900013Q00040F012Q000900010020E3000300010004000657010300120001000100040F012Q00120001001288010300053Q0006B700043Q000100012Q004D8Q00B200030002000400069A0103001200013Q00040F012Q0012000100069A0104001200013Q00040F012Q001200010020E30002000400060020E300033Q00070020E30003000300080020E300043Q00090020E30004000400080020EA00040004000A2Q00330103000300040020E300043Q00070020E30004000400060020E300053Q00090020E30005000500060020EA00050005000A2Q00330104000400052Q00330104000400022Q0036000300034Q000B012Q00013Q00013Q00013Q00030B3Q00476574477569496E73657400054Q004D7Q00208D5Q00012Q0051012Q00014Q0091017Q000B012Q00017Q00043Q0003053Q007063612Q6C03043Q007461736B03043Q0077616974026Q33D33F011C4Q00E700016Q004D00025Q00069A0102001400013Q00040F012Q00140001001288010200013Q0006B700033Q000100052Q004D3Q00014Q0046017Q004D3Q00024Q004D8Q0046012Q00014Q0033000200020001001288010200023Q0020E3000200020003001216000300044Q003300020002000100069A2Q01001400013Q00040F012Q001400012Q00E7000200014Q00DA000200024Q00E700025Q001288010300013Q0006B700040001000100022Q0046017Q0046012Q00024Q00330003000200012Q00DA000200024Q000B012Q00013Q00023Q00073Q0003123Q0053656E644D6F7573654D6F76654576656E7403043Q0067616D6503043Q007461736B03043Q0077616974029A5Q99A93F03143Q0053656E644D6F75736542752Q746F6E4576656E74029Q002A4Q004D8Q004D000100014Q00B23Q000200012Q004D000200024Q004601036Q0046010400014Q00EE0002000400012Q004D000200033Q00208D0002000200012Q004601046Q0046010500013Q001288010600024Q00EE000200060001001288010200033Q0020E3000200020004001216000300054Q00330002000200012Q004D000200033Q00208D0002000200062Q004601046Q0046010500013Q001216000600074Q00E7000700013Q001288010800023Q001216000900074Q00EE000200090001001288010200033Q0020E3000200020004001216000300054Q00330002000200012Q004D000200033Q00208D0002000200062Q004601046Q0082010500013Q00122Q000600076Q00075Q00122Q000800023Q00122Q000900076Q0002000900014Q000200016Q000200048Q00017Q00093Q00030E3Q00676574636F2Q6E656374696F6E7303063Q0069706169727303113Q004D6F75736542752Q746F6E31436C69636B03093Q0041637469766174656403103Q004D6F75736542752Q746F6E31446F776E030E3Q004D6F75736542752Q746F6E31557003053Q007063612Q6C03043Q007479706503053Q007461626C65002B3Q001288012Q00013Q00069A012Q002A00013Q00040F012Q002A0001001288012Q00024Q00132Q0100043Q00121C000200033Q00122Q000300043Q00122Q000400053Q00122Q000500066Q0001000400012Q00B23Q0002000200040F012Q00280001001288010500073Q0006B700063Q000100022Q004D8Q0046012Q00044Q00B200050002000600069A0105002700013Q00040F012Q00270001001288010700084Q0046010800064Q009C010700020002002681010700270001000900040F012Q00270001001288010700024Q0046010800064Q00B200070002000900040F012Q00250001001288010C00073Q0006B7000D0001000100012Q0046012Q000B4Q009C010C0002000200069A010C002400013Q00040F012Q002400012Q00E7000C00014Q00B8000C00014Q000F000A5Q00062B0007001C0001000200040F012Q001C00012Q000F00035Q00062B3Q000C0001000200040F012Q000C00012Q000B012Q00013Q00023Q00013Q00030E3Q00676574636F2Q6E656374696F6E7300073Q001288012Q00014Q004D00016Q004D000200014Q00730001000100022Q0051012Q00014Q0091017Q000B012Q00017Q00013Q0003043Q004669726500044Q004D7Q00208D5Q00012Q00333Q000200012Q000B012Q00017Q00113Q00030E3Q0046696E6446697273744368696C6403093Q00506C6179657247756903063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q00546578744C6162656C030A3Q005465787442752Q746F6E03043Q0054657874034Q0003073Q0056697369626C65030E3Q00497344657363656E64616E744F6603063Q00737472696E6703043Q0066696E64026Q00F03F00030B3Q00496D61676542752Q746F6E03063Q00506172656E7402624Q004D00025Q00208D000200020001001216000400024Q00FC000200040002000657010200080001000100040F012Q000800012Q0062000300034Q00DA000300023Q001288010300033Q00208D0004000200042Q00DE000400054Q003501033Q000500040F012Q005D000100208D000800070005001216000A00064Q00FC0008000A0002000657010800170001000100040F012Q0017000100208D000800070005001216000A00074Q00FC0008000A000200069A0108005D00013Q00040F012Q005D00010020E300080007000800267B0008005D0001000900040F012Q005D00010020E300080007000A00069A0108005D00013Q00040F012Q005D000100208D00080007000B2Q004D000A00014Q00FC0008000A00020006570108005D0001000100040F012Q005D00012Q004D000800024Q0046010900074Q0046010A00024Q00FC0008000A000200069A0108005D00013Q00040F012Q005D00012Q004D000800033Q0020E30009000700082Q009C010800020002001288010900034Q0046010A6Q00B200090002000B00040F012Q005B00012Q0062000E000E3Q00069A2Q01003700013Q00040F012Q003700010006AD000800350001000D00040F012Q003500012Q0011010E6Q00E7000E00013Q00040F012Q00420001001288010F000C3Q0020E3000F000F000D2Q0046011000084Q00460111000D3Q0012160012000E4Q00E7001300014Q00FC000F00130002002681010F00410001000F00040F012Q004100012Q0011010E6Q00E7000E00013Q00069A010E005B00013Q00040F012Q005B00012Q0046010F00073Q00069A010F005500013Q00040F012Q005500010006AD000F00550001000200040F012Q0055000100208D0010000F0005001216001200074Q00FC001000120002000657011000550001000100040F012Q0055000100208D0010000F0005001216001200104Q00FC001000120002000657011000550001000100040F012Q005500010020E3000F000F001100040F012Q00450001000627000F00580001000200040F012Q005800012Q0062000F000F4Q0046011000074Q00460111000F4Q0036001000033Q00062B0009002F0001000200040F012Q002F000100062B0003000D0001000200040F012Q000D00012Q0062000300034Q00DA000300024Q000B012Q00019Q002Q00020F4Q004D00026Q004601036Q0046010400014Q0076000200040003000657010200080001000100040F012Q000800012Q00E700046Q00DA000400024Q004D000400013Q00068E0005000C0001000300040F012Q000C00012Q0046010500024Q0051010400054Q009101046Q000B012Q00017Q00083Q00030E3Q0046696E6446697273744368696C6403063Q005175657374732Q033Q00497341030C3Q004D6F64756C6553637269707403053Q007063612Q6C03073Q007265717569726503043Q007479706503053Q007461626C65001F4Q004D7Q00069A012Q000500013Q00040F012Q000500012Q004D8Q00DA3Q00024Q004D3Q00013Q00208D5Q0001001216000200024Q00FC3Q0002000200069A012Q001C00013Q00040F012Q001C000100208D00013Q0003001216000300044Q00FC00010003000200069A2Q01001C00013Q00040F012Q001C00010012882Q0100053Q001288010200064Q004601036Q007600010003000200069A2Q01001C00013Q00040F012Q001C0001001288010300074Q0046010400024Q009C0103000200020026810103001C0001000800040F012Q001C00012Q00B800026Q004D00016Q00DA000100024Q000B012Q00017Q00123Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030C3Q005F576F726C644F726967696E030B3Q00456E656D79537061776E7303063Q00737472696E6703053Q006C6F77657203063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103083Q00426173655061727403043Q004E616D6503053Q007461626C6503063Q00696E73657274028Q002Q033Q00737562026Q00F03F026Q00104003043Q0066696E64016E4Q007D00015Q00122Q000200013Q00202Q00020002000200122Q000400036Q00020004000200062Q0003000A0001000200040F012Q000A000100208D000300020002001216000500044Q00FC0003000500020006570103000D0001000100040F012Q000D00012Q00DA000100023Q0006B700043Q000100012Q0046012Q00033Q001288010500053Q0020E30005000500062Q004601066Q009C0105000200022Q004D00066Q004601076Q009C010600020002001288010700073Q00208D0008000300082Q00DE000800094Q003501073Q000900040F012Q002A000100208D000C000B0009001216000E000A4Q00FC000C000E000200069A010C002A00013Q00040F012Q002A00012Q004D000C5Q0020E3000D000B000B2Q009C010C00020002000627000C002A0001000600040F012Q002A0001001288010C000C3Q0020E3000C000C000D2Q0046010D00014Q0046010E000B4Q00EE000C000E000100062B0007001B0001000200040F012Q001B00012Q00D0000700013Q0026810107004A0001000E00040F012Q004A0001001288010700073Q00208D0008000300082Q00DE000800094Q003501073Q000900040F012Q0048000100208D000C000B0009001216000E000A4Q00FC000C000E000200069A010C004800013Q00040F012Q00480001001288010C00053Q0020E3000C000C000F2Q004D000D5Q0020E3000E000B000B2Q009C010D00020002001216000E00104Q00D0000F00064Q00FC000C000F0002000627000C00480001000600040F012Q00480001001288010C000C3Q0020E3000C000C000D2Q0046010D00014Q0046010E000B4Q00EE000C000E000100062B000700340001000200040F012Q003400012Q00D0000700013Q0026810107006C0001000E00040F012Q006C00012Q00D0000700063Q000EF30011006C0001000700040F012Q006C0001001288010700073Q00208D0008000300082Q00DE000800094Q003501073Q000900040F012Q006A000100208D000C000B0009001216000E000A4Q00FC000C000E000200069A010C006A00013Q00040F012Q006A0001001288010C00053Q002097000C000C00124Q000D5Q00202Q000E000B000B4Q000D000200024Q000E00063Q00122Q000F00106Q001000016Q000C0010000200062Q000C006A00013Q00040F012Q006A0001001288010C000C3Q0020E3000C000C000D2Q0046010D00014Q0046010E000B4Q00EE000C000E000100062B000700550001000200040F012Q005500012Q00DA000100024Q000B012Q00013Q00013Q000B3Q0003063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103083Q00426173655061727403063Q00737472696E6703043Q0066696E6403053Q006C6F77657203043Q004E616D65026Q00F03F03053Q007461626C6503063Q00696E7365727401214Q001800015Q00122Q000200016Q00035Q00202Q0003000300024Q000300046Q00023Q000400044Q001D000100208D000700060003001216000900044Q00FC00070009000200069A0107001D00013Q00040F012Q001D0001001288010700053Q00209100070007000600122Q000800053Q00202Q00080008000700202Q0009000600084Q0008000200024Q00095Q00122Q000A00096Q000B00016Q0007000B000200062Q0007001D00013Q00040F012Q001D00010012880107000A3Q0020E300070007000B2Q0046010800014Q0046010900064Q00EE00070009000100062B000200070001000200040F012Q000700012Q00DA000100024Q000B012Q00017Q00073Q0003063Q00737472696E6703043Q0066696E6403053Q006C6F77657203083Q00746F737472696E6703093Q007375626D6572676564026Q00F03F0001123Q001282000100013Q00202Q00010001000200122Q000200013Q00202Q00020002000300122Q000300046Q00048Q000300046Q00023Q000200122Q000300053Q00122Q000400066Q000500016Q00010005000200262Q0001000F0001000700040F012Q000F00012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q001B3Q00031D3Q006D6F64756C6F20646520717565737473206E616F2063612Q7265676F7503053Q00706169727303043Q007479706503053Q007461626C6503083Q004C6576656C52657103063Q006E756D62657203043Q005461736B026Q00F03F025Q00E08540027Q0040025Q00709740026Q0008402Q033Q006D6F6203083Q00746F737472696E6703053Q00636F756E7403043Q00736F727403063Q0069706169727303063Q00696E7365727403043Q006E616D652Q033Q006964782Q033Q00726571028Q0003043Q006D61746803043Q006875676503083Q00506F736974696F6E03093Q004D61676E697475646503283Q006E656E68756D612071756573742070617261206F20736575206C6576656C206E65737465206D617202D14Q004D00026Q0065010200010002000657010200070001000100040F012Q000700012Q0062000300033Q001216000400014Q0036000300034Q004D000300014Q00610103000100012Q004100035Q00122Q000400026Q000500026Q00040002000600044Q007E0001001288010900034Q0046010A00084Q009C0109000200020026810109007E0001000400040F012Q007E0001001288010900024Q0046010A00084Q00B200090002000B00040F012Q007C0001001288010E00034Q0046010F000D4Q009C010E00020002002681010E007C0001000400040F012Q007C0001001288010E00033Q0020E3000F000D00052Q009C010E00020002002681010E007C0001000600040F012Q007C00010020E3000E000D00050006F2000E007C00013Q00040F012Q007C0001001288010E00033Q0020E3000F000D00072Q009C010E00020002002681010E007C0001000400040F012Q007C00010020E3000E000D00052Q00E7000F00014Q004D001000023Q002681011000310001000800040F012Q00310001000EF3000900310001000E00040F012Q003100012Q00E7000F6Q004D001000023Q002681011000390001000A00040F012Q003900010026F1000E00380001000900040F012Q00380001000EF3000B00390001000E00040F012Q003900012Q00E7000F6Q004D001000023Q0026810110003F0001000C00040F012Q003F0001002695000E003F0001000B00040F012Q003F00012Q00E7000F6Q001301105Q001288011100023Q0020E30012000D00072Q00B200110002001300040F012Q00540001001288011600034Q0046011700154Q009C011600020002002681011600540001000600040F012Q00540001000ED3000800540001001500040F012Q005400012Q00D0001600103Q0020AC0116001600082Q001301173Q00020012880118000E4Q0046011900144Q009C01180002000200105D0117000D001800105D0117000F00152Q009E00100016001700062B001100440001000200040F012Q00440001001288011100043Q0020E30011001100102Q0046011200103Q0006B700133Q000100012Q004D3Q00034Q00EE0011001300012Q0062001100113Q001288011200114Q0046011300104Q00B200120002001400040F012Q006C000100069A2Q01006A00013Q00040F012Q006A00012Q0046011700014Q00E8001800033Q00202Q00190016000D4Q001800196Q00173Q000200062Q0017006C00013Q00040F012Q006C00012Q0046011100163Q00040F012Q006E000100062B001200610001000200040F012Q0061000100069A010F007C00013Q00040F012Q007C000100069A0111007C00013Q00040F012Q007C0001001288011200043Q0020AE0112001200124Q001300036Q00143Q000400102Q00140013000700102Q00140014000C00102Q00140015000E00202Q00150011000D00102Q0014000D00154Q00120014000100062B000900170001000200040F012Q0017000100062B0004000E0001000200040F012Q000E0001001288010400043Q0020E30004000400102Q0046010500033Q000285000600014Q00EE0004000600012Q0087010400046Q0004000100024Q000500073Q00122Q000800116Q000900036Q00080002000A00044Q00C3000100069A0105009200013Q00040F012Q009200010020E3000D000C0015000676010D00920001000500040F012Q0092000100040F012Q00C500012Q004D000D00053Q0020E3000E000C000D2Q009C010D000200022Q00D0000E000D3Q000EA7011600A60001000E00040F012Q00A600012Q004D000E00063Q0020E3000F000C000D2Q009C010E000200022Q00D0000E000E3Q000EA7011600A60001000E00040F012Q00A600012Q004D000E00023Q002681010E00C30001000C00040F012Q00C300012Q004D000E00073Q0020E3000F000C00132Q009C010E0002000200069A010E00C300013Q00040F012Q00C300010020E30005000C0015001216000E00163Q00069A010400BC00013Q00040F012Q00BC00012Q00D0000F000D3Q000ED3001600BC0001000F00040F012Q00BC0001001288010F00173Q0020E3000E000F0018001288010F00114Q00460110000D4Q00B2000F0002001100040F012Q00BA00010020E30014001300190020E30015000400192Q00320114001400150020E300140014001A000676011400BA0001000E00040F012Q00BA00012Q0046010E00143Q00062B000F00B30001000200040F012Q00B3000100069A010700C000013Q00040F012Q00C00001000676010E00C30001000700040F012Q00C300012Q0046010F000C4Q00460107000E4Q00460106000F3Q00062B0008008C0001000200040F012Q008C000100069A010600C800013Q00040F012Q00C800012Q00DA000600024Q00D0000800033Q000ED3001600CD0001000800040F012Q00CD00010020E30008000300082Q00DA000800024Q0062000800083Q0012160009001B4Q0036000800034Q000B012Q00013Q00023Q00013Q002Q033Q006D6F62020C4Q001401025Q00202Q00033Q00014Q0002000200024Q00035Q00202Q0004000100014Q00030002000200062Q000200090001000300040F012Q000900012Q001101026Q00E7000200014Q00DA000200024Q000B012Q00017Q00013Q002Q033Q0072657102083Q0020E300023Q00010020E3000300010001000639010300050001000200040F012Q000500012Q001101026Q00E7000200014Q00DA000200024Q000B012Q00017Q00053Q00030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F7450617274030B3Q005072696D6172795061727403163Q0046696E6446697273744368696C64576869636849734103083Q004261736550617274010E3Q00208D00013Q0001001216000300024Q00FC0001000300020006572Q01000C0001000100040F012Q000C00010020E300013Q00030006572Q01000C0001000100040F012Q000C000100208D00013Q0004001216000300054Q00E7000400014Q00FC0001000400022Q00DA000100024Q000B012Q00017Q000D3Q00025Q00E0854003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403073Q00456E656D69657303043Q004E50437303063Q00697061697273030B3Q004765744368696C6472656E03053Q007063612Q6C03183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C03153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F69642Q01034B3Q000657012Q00040001000100040F012Q000400012Q0062000300034Q00DA000300023Q0006572Q0100070001000100040F012Q00070001001216000100013Q001288010300023Q00208D000300030003001216000500044Q00FC0003000500022Q0062000400053Q0006B700063Q000100092Q0046012Q00034Q004D8Q004D3Q00014Q004D3Q00024Q0046012Q00024Q0046017Q0046012Q00014Q0046012Q00054Q0046012Q00043Q001289000700023Q00202Q00070007000300122Q000900056Q00070009000200062Q0007002600013Q00040F012Q00260001001288010800063Q00208D0009000700072Q00DE0009000A4Q003501083Q000A00040F012Q002400012Q0046010D00064Q0046010E000C4Q0033000D0002000100062B000800210001000200040F012Q00210001000657010400490001000100040F012Q00490001001288010800083Q0006B700090001000100022Q0046017Q0046012Q00014Q00B200080002000900069A0108004900013Q00040F012Q0049000100069A0109004900013Q00040F012Q004900012Q0013010A5Q001288010B00064Q0046010C00094Q00B2000B0002000D00040F012Q0047000100208D0010000F00090012160012000A4Q00FC00100012000200069A0110004700013Q00040F012Q004700012Q00730011000A0010000657011100470001000100040F012Q0047000100208D00110010000B0012160013000C4Q00FC00110013000200069A0111004700013Q00040F012Q0047000100202C000A0010000D2Q0046011100064Q0046011200104Q003300110002000100062B000B00360001000200040F012Q003600012Q00DA000400024Q000B012Q00013Q00023Q00133Q002Q033Q0049734103053Q004D6F64656C030E3Q00497344657363656E64616E744F6603163Q00476574506C6179657246726F6D43686172616374657203043Q004E616D65030E3Q0046696E6446697273744368696C6403083Q0051756573742Q42470003063Q00737472696E6703043Q0066696E6403053Q007175657374026Q00F03F03153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403083Q00506F736974696F6E03093Q004D61676E6974756465025Q00C0724003093Q007375626D6172696E65025Q00409F40015F3Q00208D00013Q0001001216000300024Q00FC0001000300020006572Q0100060001000100040F012Q000600012Q000B012Q00014Q004D00015Q00069A2Q01000F00013Q00040F012Q000F000100208D00013Q00032Q004D00036Q00FC00010003000200069A2Q01000F00013Q00040F012Q000F00012Q000B012Q00014Q004D000100013Q00208D0001000100042Q004601036Q00FC00010003000200069A2Q01001600013Q00040F012Q001600012Q000B012Q00014Q004D000100024Q004601026Q009C2Q01000200020006572Q01001C0001000100040F012Q001C00012Q000B012Q00014Q004D000200033Q0020E300033Q00052Q009C01020002000200208D00033Q0006001216000500074Q00E7000600014Q00FC0003000600020026810103002F0001000800040F012Q002F0001001288010300093Q00203D00030003000A4Q000400023Q00122Q0005000B3Q00122Q0006000C6Q000700016Q00030007000200262Q0003002F0001000800040F012Q002F00012Q001101036Q00E7000300013Q0006570103003B0001000100040F012Q003B00012Q004D000400043Q00069A0104003A00013Q00040F012Q003A000100208D00043Q000D0012160006000E4Q00FC0004000600020006570104003B0001000100040F012Q003B00012Q000B012Q00013Q0020E300040001000F2Q00D4000500056Q00040004000500202Q0004000400104Q000500063Q00062Q000500430001000400040F012Q004300012Q000B012Q00014Q0046010500043Q0020DC00063Q000600122Q000800076Q000900016Q00060009000200062Q0006004B00013Q00040F012Q004B0001002078000500050011001288010600093Q0020A600060006000A4Q000700023Q00122Q000800123Q00122Q0009000C6Q000A00016Q0006000A000200062Q0006005500013Q00040F012Q005500010020AC0105000500132Q004D000600073Q00069A0106005B00013Q00040F012Q005B00012Q004D000600073Q0006760105005E0001000600040F012Q005E00012Q0046010600014Q00B8000500074Q00B8000600084Q000B012Q00017Q00073Q0003093Q00776F726B737061636503153Q0047657450617274426F756E6473496E52616469757303043Q006D6174682Q033Q006D696E025Q00408F40030D3Q004F7665726C6170506172616D732Q033Q006E6577000E3Q001237012Q00013Q00206Q00024Q00025Q00122Q000300033Q00202Q0003000300044Q000400013Q00122Q000500056Q00030005000200122Q000400063Q00202Q0004000400074Q000400019Q009Q008Q00017Q00063Q00030E3Q0046696E6446697273744368696C6403053Q005175657374002Q033Q0049734103093Q004775694F626A65637403073Q0056697369626C6500144Q004D8Q0065012Q000100020006210001000700013Q00040F012Q0007000100208D00013Q0001001216000300024Q00FC00010003000200267B000100100001000300040F012Q0010000100208D000200010004001216000400054Q00FC00020004000200069A0102001200013Q00040F012Q001200010020E300020001000600040F012Q001200012Q001101026Q00E7000200014Q00DA000200024Q000B012Q00017Q000C3Q00030E3Q0046696E6446697273744368696C6403093Q00506C61796572477569034Q0003063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q00546578744C6162656C03043Q0054657874030E3Q00497344657363656E64616E744F6603063Q00737472696E6703043Q0066696E64026Q00F03F013A4Q004D00015Q00208D000100010001001216000300024Q00FC0001000300020006572Q0100080001000100040F012Q000800012Q00E700026Q00DA000200024Q004D000200014Q004601036Q009C0102000200020026810102000F0001000300040F012Q000F00012Q00E700036Q00DA000300023Q001288010300043Q00208D0004000100052Q00DE000400054Q003501033Q000500040F012Q0035000100208D000800070006001216000A00074Q00FC0008000A000200069A0108003500013Q00040F012Q003500010020E300080007000800267B000800350001000300040F012Q0035000100208D0008000700092Q004D000A00024Q00FC0008000A0002000657010800350001000100040F012Q003500012Q004D000800034Q0046010900074Q0046010A00014Q00FC0008000A000200069A0108003500013Q00040F012Q003500012Q004D000800013Q0020E30009000700082Q009C0108000200020012880109000A3Q00201801090009000B4Q000A00086Q000B00023Q00122Q000C000C6Q000D00016Q0009000D000200062Q0009003500013Q00040F012Q003500012Q00E7000900014Q00DA000900023Q00062B000300140001000200040F012Q001400012Q00E700036Q00DA000300024Q000B012Q00017Q000F3Q00030E3Q0046696E6446697273744368696C6403093Q00506C61796572477569034Q0003063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103093Q00546578744C6162656C03043Q0054657874030E3Q00497344657363656E64616E744F6603063Q00737472696E6703043Q0066696E64026Q00F03F03053Q006D6174636803113Q002825642B2925732A2F25732A2825642B2903083Q00746F6E756D62657201454Q004D00015Q00208D000100010001001216000300024Q00FC0001000300022Q004D000200014Q004601036Q009C01020002000200069A2Q01000B00013Q00040F012Q000B00010026810102000D0001000300040F012Q000D00012Q0062000300034Q00DA000300023Q001288010300043Q00208D0004000100052Q00DE000400054Q003501033Q000500040F012Q0040000100208D000800070006001216000A00074Q00FC0008000A000200069A0108004000013Q00040F012Q004000010020E300080007000800267B000800400001000300040F012Q0040000100208D0008000700092Q004D000A00024Q00FC0008000A0002000657010800400001000100040F012Q004000012Q004D000800034Q0046010900074Q0046010A00014Q00FC0008000A000200069A0108004000013Q00040F012Q004000010012880108000A3Q00209700080008000B4Q000900013Q00202Q000A000700084Q0009000200024Q000A00023Q00122Q000B000C6Q000C00016Q0008000C000200062Q0008004000013Q00040F012Q004000010012880108000A3Q0020E300080008000D0020E3000900070008001216000A000E4Q00760008000A000900069A0108004000013Q00040F012Q0040000100069A0109004000013Q00040F012Q00400001001288010A000F4Q0046010B00084Q009C010A00020002001288010B000F4Q0046010C00094Q00DE000B000C4Q0091010A5Q00062B000300120001000200040F012Q001200012Q0062000300034Q00DA000300024Q000B012Q00019Q002Q0001054Q00722Q018Q00028Q000100026Q00019Q0000017Q00143Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403073Q00456E656D696573034Q0003063Q00697061697273030B3Q004765744368696C6472656E03043Q004E616D6503063Q00737472696E672Q033Q00737562026Q00F03F03153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403103Q0048756D616E6F6964522Q6F745061727403063Q004865616C7468028Q0003053Q007461626C6503063Q00696E7365727403013Q006D03013Q006803013Q007001374Q00132Q015Q001288010200013Q00208D000200020002001216000400034Q00FC000200040002000657010200080001000100040F012Q000800012Q00DA000100024Q004D00036Q004601046Q009C0103000200020026810103000E0001000400040F012Q000E00012Q00DA000100023Q001288010400053Q00208D0005000200062Q00DE000500064Q003501043Q000600040F012Q003300012Q004D00095Q00202B010A000800074Q00090002000200122Q000A00083Q00202Q000A000A00094Q000B00093Q00122Q000C000A6Q000D00036Q000A000D000200062Q000A00330001000300040F012Q0033000100208D000A0008000B0012BB000C000C6Q000A000C000200202Q000B0008000200122Q000D000D6Q000B000D000200062Q000A003300013Q00040F012Q0033000100069A010B003300013Q00040F012Q003300010020E3000C000A000E000ED3000F00330001000C00040F012Q00330001001288010C00103Q002028000C000C00114Q000D00016Q000E3Q000300102Q000E0012000800102Q000E0013000A00102Q000E0014000B4Q000C000E000100062B000400130001000200040F012Q001300012Q00DA000100024Q000B012Q00017Q000B3Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403043Q004E50437303063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03043Q004E616D6503083Q00506F736974696F6E03093Q004D61676E6974756465025Q00709740002D4Q004D8Q0065012Q00010002000657012Q00060001000100040F012Q000600012Q00E700016Q00DA000100023Q0012882Q0100013Q00208D000100010002001216000300034Q00FC00010003000200069A2Q01002A00013Q00040F012Q002A0001001288010200043Q00208D0003000100052Q00DE000300044Q003501023Q000400040F012Q0028000100208D000700060006001216000900074Q00FC00070009000200069A0107002800013Q00040F012Q002800012Q004D000700013Q0020E30008000600082Q009C01070002000200069A0107002800013Q00040F012Q002800012Q004D000700024Q0046010800064Q009C01070002000200069A0107002800013Q00040F012Q002800010020E30008000700090020E300093Q00092Q00320108000800090020E300080008000A002695000800280001000B00040F012Q002800012Q00E7000800014Q00DA000800023Q00062B000200110001000200040F012Q001100012Q00E700026Q00DA000200024Q000B012Q00017Q00193Q0003023Q006F7303053Q00636C6F636B03043Q007461736B03043Q0077616974027Q0040030F3Q007375626D6172696E65776F726B657203043Q0074696B6903123Q006F205375626D6172696E6520576F726B6572026Q002E4003353Q006E616F206163686569206F205375626D6172696E6520576F726B6572202853756220506F72742C2054696B69204F7574706F73742903213Q0066616C616E646F20636F6D206F205375626D6172696E6520576F726B65723Q2E03083Q00506F736974696F6E03173Q0052462F5375626D6172696E65576F726B6572537065616B03053Q007063612Q6C026Q00044003143Q005375626D6172696E65576F726B6572537065616B03173Q0054726176656C546F5375626D657267656449736C616E6403183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C026Q00F03F026Q0008402Q033Q007965732Q033Q0073696D026Q00344003493Q006E616F20636F6E736567756920656E74726172206E6120696C6861202870726563697361207465722064652Q726F7461646F206F20547972616E74206F662074686520536B69657329028F4Q004D00026Q006501020001000200069A0102000600013Q00040F012Q000600012Q00E7000200014Q00DA000200023Q001288010200013Q0020E30002000200022Q00650102000100022Q004D000300013Q000676010200150001000300040F012Q001500012Q0046010200014Q004D000300024Q0033000200020001001288010200033Q0020E3000200020004001216000300054Q00330002000200012Q00E700026Q00DA000200024Q004D000200034Q0013010300013Q001216000400064Q00230103000100012Q0013010400013Q001216000500074Q00230104000100012Q004601056Q0046010600013Q001216000700084Q00FC0002000700020006570102002B0001000100040F012Q002B0001001288010300013Q0020CB0003000300024Q00030001000200202Q00030003000900122Q0004000A6Q000400026Q000300016Q00038Q000300024Q0046010300013Q00126F0104000B6Q0003000200014Q000300046Q00030001000200062Q000400330001000300040F012Q003300010020E300040003000C0006B700053Q000100022Q004D3Q00044Q0046012Q00044Q004D000600053Q0012160007000D4Q009C01060002000200069A0106003F00013Q00040F012Q003F00010012880107000E3Q0006B700080001000100012Q0046012Q00064Q0033000700020001001288010700033Q0020E30007000700040012160008000F4Q00330007000200012Q0046010700054Q006501070001000200069A0107004900013Q00040F012Q004900012Q00E7000700014Q00DA000700024Q004D000700063Q001216000800103Q001216000900114Q00EE000700090001001288010700033Q0020E30007000700040012160008000F4Q00330007000200012Q0046010700054Q006501070001000200069A0107005700013Q00040F012Q005700012Q00E7000700014Q00DA000700023Q00208D000700020012001216000900134Q00FC000700090002001216000800143Q001216000900153Q001216000A00143Q0004630008008200012Q004D000C00074Q0046010D00074Q0033000C00020001001288010C00033Q0020E3000C000C0004001216000D00144Q0033000C000200012Q004D000C00084Q0013010D00023Q001216000E00163Q001216000F00174Q0023010D000200012Q00E7000E00014Q00EE000C000E0001001288010C00033Q0020E3000C000C0004001216000D00144Q0033000C000200012Q004D000C00084Q0013010D00023Q001216000E00163Q001216000F00174Q0023010D000200012Q00E7000E00014Q00EE000C000E0001001288010C00033Q0020E3000C000C0004001216000D000F4Q0033000C000200012Q0046010C00054Q0065010C0001000200069A010C008100013Q00040F012Q008100012Q00E7000C00014Q00DA000C00023Q0004060108005E0001001288010800013Q00209D0108000800024Q00080001000200202Q00080008001800122Q000900196Q000900026Q000800016Q000800016Q000900026Q0008000200014Q00086Q00DA000800024Q000B012Q00013Q00023Q00044Q0003083Q00506F736974696F6E03093Q004D61676E6974756465025Q0070974000114Q004D8Q0065012Q0001000200267B3Q000D0001000100040F012Q000D00012Q004D000100013Q00267B0001000D0001000100040F012Q000D00010020E300013Q00022Q004D000200014Q00322Q01000100020020E3000100010003000EA70104000E0001000100040F012Q000E00012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00023Q00030C3Q00496E766F6B6553657276657203173Q0054726176656C546F5375626D657267656449736C616E6400054Q0075016Q00206Q000100122Q000200028Q000200016Q00017Q000E3Q0003083Q00506F736974696F6E03093Q004D61676E6974756465027Q004003043Q006D6174682Q033Q006D696E025Q00E0854003043Q00556E697403063Q00434672616D652Q033Q006E657703013Q005803013Q0059026Q004E4003013Q005A030A3Q0074772Q656E53702Q6564032D4Q004D00036Q0065010300010002000657010300060001000100040F012Q000600012Q00E700046Q00DA000400023Q0020E30004000300012Q003201043Q00040020E30005000400020026950005000D0001000300040F012Q000D00012Q00E7000500014Q00DA000500023Q001288010500043Q0020E30005000500050020E3000600040002001216000700064Q00FC0005000700020020E30006000300010020E30007000400072Q00600007000700052Q00330106000600072Q004D000700013Q001288010800083Q0020E30008000800090020E300090006000A0020E3000A00040002000ED3000600240001000A00040F012Q002400010020E3000A3Q000B00068E000B00210001000200040F012Q00210001001216000B000C4Q0033010A000A000B000657010A00250001000100040F012Q002500010020E3000A3Q000B0020E3000B0006000D2Q00950108000B00024Q000900023Q00202Q00090009000E4Q000A00016Q0007000A6Q00079Q0000017Q002F3Q002Q033Q006D6F62028Q0003043Q006E616D6503043Q007461736B03043Q0077616974027Q004003063Q0069706169727303083Q00506F736974696F6E03093Q004D61676E69747564652Q033Q006C6F6303103Q006E656E68756D20737061776E2064652003153Q0020656E636F6E747261646F206E65737465206D617203093Q00696E646F206174652003023Q00202803043Q006D61746803053Q00666C2Q6F7203073Q0020737475647329026Q008940026Q004E4003063Q00434672616D652Q033Q006E6577026Q002840030A3Q0074772Q656E53702Q6564029A5Q99B93F03013Q0070026Q00444003023Q006F7303053Q00636C6F636B026Q003940026Q00E03F03063Q00776561706F6E03083Q007573655175657374026Q66D63F0003093Q006E2Q656451756573742Q01026Q00F03F2Q033Q004C76202Q033Q00207C2003063Q002028726571202Q033Q0072657103043Q0029207C2003023Q00782003013Q0068030A3Q006F72696F6E436C69636B027B14AE47E17A843F03083Q0061746B44656C61790648013Q00B800066Q004D000600014Q0065010600010002000657010600060001000100040F012Q000600012Q000B012Q00014Q004D000700023Q0020E300083Q00012Q009C0107000200022Q00D0000800073Q0026810108007D0001000200040F012Q007D00012Q004D000800033Q0020E300093Q00032Q009C01080002000200069A0108002000013Q00040F012Q002000012Q004D000800044Q0065010800010002000657010800200001000100040F012Q002000012Q004D000800054Q0046010900044Q0046010A00054Q00FC0008000A000200069A0108001F00013Q00040F012Q001F0001001288010800043Q0020E3000800080005001216000900064Q00330008000200012Q000B012Q00014Q004D000800063Q00206001093Q00014Q0008000200024Q000900096Q000A00083Q000E2Q0002003A0001000A00040F012Q003A00012Q0062000A000A3Q001288010B00074Q0046010C00084Q00B2000B0002000D00040F012Q003700010020E30010000F00080020E30011000600082Q00320110001000110020E300100010000900069A010A003400013Q00040F012Q00340001000676011000370001000A00040F012Q003700010020E30011000F00082Q0046010A00104Q0046010900113Q00062B000B002C0001000200040F012Q002C000100040F012Q004900010020E3000A0002000A00069A010A004900013Q00040F012Q00490001001288010A00073Q0020E3000B0002000A2Q00B2000A0002000C00040F012Q00470001000657010900470001000100040F012Q004700012Q004D000F00074Q00460110000E4Q009C010F000200022Q00460109000F3Q00062B000A00410001000200040F012Q00410001000657010900560001000100040F012Q005600012Q0046010A00053Q001262010B000B3Q00202Q000C3Q000100122Q000D000C6Q000B000B000D4Q000A0002000100122Q000A00043Q00202Q000A000A000500122Q000B00066Q000A000200016Q00013Q0020E3000A000600082Q0032010A0009000A0020E3000A000A00092Q0046010B00053Q001213000C000D3Q00202Q000D3Q000100122Q000E000E3Q00122Q000F000F3Q00202Q000F000F00104Q0010000A6Q000F0002000200122Q001000116Q000C000C00104Q000B00020001000ED30012006C0001000A00040F012Q006C00012Q004D000B00084Q003A010C00096Q000D00043Q00122Q000E00136Q000B000E000100044Q007800012Q004D000B00093Q001288010C00143Q0020E3000C000C00152Q004D000D000A4Q0046010E00093Q001216000F00164Q00A1010D000F4Q0004000C3Q00022Q004D000D000B3Q0020E3000D000D00172Q0046010E00044Q00EE000B000E0001001288010B00043Q0020E3000B000B0005001216000C00184Q0033000B000200012Q000B012Q00013Q0020E300083Q00012Q00B800086Q0062000800093Q001288010A00074Q0046010B00074Q00B2000A0002000C00040F012Q009000010020E3000F000E0019002064010F000F000800202Q0010000600084Q000F000F001000202Q000F000F000900062Q0009008D00013Q00040F012Q008D0001000676010F00900001000900040F012Q009000012Q00460110000E4Q00460109000F4Q0046010800103Q00062B000A00840001000200040F012Q008400010020E3000A000800190020E3000A000A00082Q004D000B000C4Q0061010B00010001000ED3001A00AA0001000900040F012Q00AA00012Q0046010B00053Q00124A000C000D3Q00202Q000D3Q00014Q000C000C000D4Q000B000200014Q000B00093Q00122Q000C00143Q00202Q000C000C00154Q000D000A6Q000E000A6Q000F000D4Q0077010F00014Q0043010D8Q000C3Q00024Q000D000B3Q00202Q000D000D00174Q000E00046Q000B000E0001001288010B001B3Q0020E3000B000B001C2Q0065010B00010002001288010C001B3Q0020E3000C000C001C2Q0065010C00010002001216000D00024Q0046010E00044Q0065010E0001000200069A010E00452Q013Q00040F012Q00452Q01001288010E001B3Q0020E3000E000E001C2Q0065010E000100022Q0032010E000E000B002695000E00452Q01001D00040F012Q00452Q01001288010E001B3Q0020E3000E000E001C2Q0065010E000100022Q0032010E000E000D000ED3001E00C90001000E00040F012Q00C90001001288010E001B3Q002059010E000E001C4Q000E000100024Q000D000E6Q000E000E6Q000F000B3Q00202Q000F000F001F4Q000E000200010020E3000E0002002000069A010E00F400013Q00040F012Q00F40001001288010E001B3Q0020E3000E000E001C2Q0065010E000100022Q0032010E000E000C000ED3002100F40001000E00040F012Q00F40001001288010E001B3Q002056010E000E001C4Q000E000100024Q000C000E6Q000E000F3Q00202Q000F3Q00014Q000E0002000F00062Q001000E70001000E00040F012Q00E70001000621001000E70001000F00040F012Q00E700010006F2000F00E50001000E00040F012Q00E500010012880110001B3Q0020E300100010001C2Q00650110000100022Q003201100010000B000EA7010600E60001001000040F012Q00E600012Q001101106Q00E7001000013Q002681010E00EE0001002200040F012Q00EE00012Q004D001100103Q0020E300123Q00012Q009C01110002000200069A011100F000013Q00040F012Q00F0000100069A011000F400013Q00040F012Q00F4000100069A2Q0100452Q013Q00040F012Q00452Q0100309300010023002400040F012Q00452Q012Q004D000E00023Q0020E3000F3Q00012Q009C010E000200022Q00D0000F000E3Q002681010F00FB0001000200040F012Q00FB000100040F012Q00452Q010020E3000F000E00252Q0087011000016Q0010000100024Q001100113Q00122Q001200076Q0013000E6Q00120002001400044Q00142Q0100069A0110000C2Q013Q00040F012Q000C2Q010020E30017001600190020E400170017000800202Q0018001000084Q00170017001800202Q00170017000900062Q0017000D2Q01000100040F012Q000D2Q01001216001700023Q00069A011100112Q013Q00040F012Q00112Q01000676011700142Q01001100040F012Q00142Q012Q0046011800164Q0046011100174Q0046010F00183Q00062B001200032Q01000200040F012Q00032Q010020E30012000F00190020E3000A001200082Q0046011000053Q001216001100264Q0046011200033Q001216001300273Q0020E300143Q0003001216001500283Q0020E300163Q00290012160017002A4Q00D00018000E3Q0012160019002B3Q0020E3001A3Q0001001216001B00274Q004D001C00114Q0065011C000100022Q008700110011001C2Q00330010000200012Q004D001000124Q004D0011000A4Q00460112000A4Q004D0013000D4Q0077011300014Q000400113Q00022Q00460112000A4Q00FC001000120002000657011000332Q01000100040F012Q00332Q0100040F012Q00452Q012Q004D001000134Q00610110000100012Q004D001000143Q0020E30011000F002C2Q0033001000020001001288011000043Q0020E30010001000052Q004D0011000B3Q0020E300110011002D00069A011100412Q013Q00040F012Q00412Q010012160011002E3Q000657011100432Q01000100040F012Q00432Q012Q004D0011000B3Q0020E300110011002F2Q003300100002000100040F012Q00B100012Q0062000E000E4Q00B8000E6Q000B012Q00017Q00014Q0001034Q004D00015Q00202C00013Q00012Q000B012Q00017Q00473Q0003093Q006C6173744C6576656C026Q00F0BF030B3Q00612Q73756D65556E74696C028Q0003093Q006162616E646F6E656401002Q033Q0070726503013Q007103063Q0066696C7465722Q033Q0072657103043Q006E616D652Q033Q00696478030B3Q0073656D2071756573743A2003083Q00746F737472696E6703043Q007461736B03043Q0077616974026Q00084003083Q0075736551756573742Q033Q006D6F62033C3Q00612071756573742061746976612065206465206F7574726F206D6F623B206162616E646F6E616E646F20616E74657320646520636F6E74696E756172030C3Q004162616E646F6E51756573742Q01026Q33F33F03093Q006E2Q65645175657374027Q0040026Q00F03F03083Q00506F736974696F6E03043Q006D61746803043Q006875676503063Q0069706169727303093Q004D61676E697475646503073Q00566563746F72332Q033Q006E6577026Q0079402Q033Q006D61782Q033Q006C6F6303013Q007003063Q006E7063506F7303013Q003A026Q004440025Q00208C40025Q00E085402Q033Q004C762003173Q003A20696E646F20616F204E50432064612071756573742003023Q00202803013Q002903063Q00434672616D65026Q001040030A3Q0074772Q656E53702Q6564026Q003940030A3Q006C6173744E7063506F7303093Q00207C20717565737420030C3Q0029207C20737061776E733A20030A3Q00207C2066616C74616D2003053Q00666C2Q6F7203063Q00207374756473026Q004E4000025Q0070974003013Q005803013Q005903013Q005A03473Q006E616F20636F6E73656775692063686567617220616F204E504320636F2Q7265746F3B206E616F20766F7520696E696369617220756D61207175657374206E6F2065736375726F026Q00F83F030A3Q005374617274517565737403083Q003A2071756573742003233Q0020656E76696164612C20616775617264616E646F20636F6E6669726D6163616F3Q2E027B14AE47E17AB43F03193Q006E616F20636F6E6669726D656920612071756573742064652003143Q003B2074656E74616E646F206E6F76616D656E7465026Q33D33F04E9013Q004D00046Q0073000400043Q0006570104000B0001000100040F012Q000B00012Q001301053Q000300308B00050001000200302Q00050003000400302Q0005000500064Q000400056Q00058Q00053Q00040020E300050001000700069A0105001500013Q00040F012Q001500010020E30005000100072Q0046010600024Q0046010700034Q00FC00050007000200069A0105001500013Q00040F012Q001500012Q000B012Q00014Q004D000500014Q00650105000100020020E30006000400010006270005001D0001000600040F012Q001D00010020E3000600040008000657010600590001000100040F012Q0059000100105D0104000100052Q00E5000600076Q000800026Q000900053Q00202Q000A000100094Q0008000A00094Q000600096Q000700083Q00062Q0007003400013Q00040F012Q003400010020E300080004000800069A0108003400013Q00040F012Q003400010020E300080007000A0020E30009000400080020E300090009000A000676010800340001000900040F012Q003400010020E30008000400080020E300080008000A0006F2000800340001000500040F012Q003400010020E300070004000800069A0107004300013Q00040F012Q004300010020E300080004000800069A0108004300013Q00040F012Q004300010020E300080007000B0020E30009000400080020E300090009000B000627000800430001000900040F012Q004300010020E300080007000C0020E30009000400080020E300090009000C0006AD000800440001000900040F012Q0044000100309300040005000600068E000800470001000700040F012Q004700010020E300080004000800105D010400080008000657010700590001000100040F012Q005900010020E3000800040008000657010800590001000100040F012Q005900012Q0046010800033Q0012160009000D3Q001288010A000E4Q0046010B00064Q009C010A000200022Q008700090009000A2Q00330008000200010012880108000F3Q0020E3000800080010001216000900114Q00330008000200012Q000B012Q00013Q0020E30006000400080020E300070001001200069A010700DB2Q013Q00040F012Q00DB2Q012Q004D000700034Q006501070001000200069A0107007300013Q00040F012Q007300012Q004D000700043Q0020E30008000600132Q009C010700020002000657010700730001000100040F012Q007300012Q0046010700033Q0012B1010800146Q0007000200014Q000700053Q00122Q000800156Q00070002000100302Q00040003000400302Q00040005001600122Q0007000F3Q00202Q00070007001000122Q000800176Q0007000200016Q00013Q0020E30007000400180006570107007B0001000100040F012Q007B00012Q004D000700063Q0020E30008000600132Q009C010700020002000657010700DB2Q01000100040F012Q00DB2Q012Q004D000700073Q0020E300080006000B2Q009C01070002000200069A0107009300013Q00040F012Q009300012Q004D000700084Q0065010700010002000657010700930001000100040F012Q009300012Q004D000700094Q0046010800024Q0046010900034Q00FC0007000900020006570107008F0001000100040F012Q008F00010012880107000F3Q0020E3000700070010001216000800194Q00330007000200012Q000B012Q00013Q0012880107000F3Q0020E3000700070010001216000800194Q00330007000200012Q004D0007000A3Q0020600108000600134Q0007000200024Q000800086Q000900073Q000E2Q000400D00001000900040F012Q00D000012Q004D0009000B4Q00A301090001000200202Q000A0007001A00202Q000A000A001B00122Q000B001C3Q00202Q000B000B001D00122Q000C001E6Q000D00076Q000C0002000E00044Q00B2000100069A010900AC00013Q00040F012Q00AC00010020E300110010001B0020E300120009001B2Q00320111001100120020E300110011001F000657011100AD0001000100040F012Q00AD0001001216001100043Q000676011100B20001000B00040F012Q00B200010020E300120010001B2Q0046010B00114Q0046010A00123Q00062B000C00A40001000200040F012Q00A40001001288010C00203Q0020E3000C000C0021001216000D00043Q001216000E00043Q001216000F00044Q00FC000C000F0002001216000D00043Q001288010E001E4Q0046010F00074Q00B2000E0002001000040F012Q00C700010020E300130012001B2Q003201130013000A0020E300130013001F0026AB001300C70001002200040F012Q00C700010020E300130012001B2Q0033010C000C00130020AC010D000D001A00062B000E00BF0001000200040F012Q00BF0001001288010E001C3Q00202C010E000E00234Q000F000D3Q00122Q0010001A6Q000E001000024Q0008000C000E00044Q00DF00010020E300090001002400069A010900DF00013Q00040F012Q00DF00010012880109001E3Q0020E3000A000100242Q00B200090002000B00040F012Q00DD0001000657010800DD0001000100040F012Q00DD00012Q004D000E000C4Q0046010F000D4Q009C010E000200022Q00460108000E3Q00062B000900D70001000200040F012Q00D70001000657010800EA0001000100040F012Q00EA00012Q004D0009000D3Q0020E3000A000600132Q009C0109000200020020E3000A0009001A00069A010A00EA00013Q00040F012Q00EA00010020E3000A0009001A0020E3000A000A00250020E30008000A001B2Q00E700095Q0020E3000A00040026000657010A00EF0001000100040F012Q00EF00012Q0013010A5Q00105D01040026000A0020EC000A0006000B00122Q000B00273Q00122Q000C000E3Q00202Q000D0006000C4Q000C000200024Q000A000A000C00202Q000B000400264Q000B000B000A00062Q000B00FC00013Q00040F012Q00FC00010020E3000B000400262Q00730008000B000A001216000B001A3Q001216000C00283Q001216000D001A3Q000463000B00952Q012Q0046010F00024Q0065010F00010002000657010F00052Q01000100040F012Q00052Q012Q000B012Q00014Q004D000F000B4Q0065010F0001000200069A010F00952Q013Q00040F012Q00952Q010006570108000C2Q01000100040F012Q000C2Q0100040F012Q00952Q010020E30010000400262Q007300100010000A00069A011000162Q013Q00040F012Q00162Q012Q001301103Q00010020E30011000400262Q007300110011000A00105D0110001B00110006570110002B2Q01000100040F012Q002B2Q012Q004D0010000E4Q0046011100083Q000ED30011001D2Q01000E00040F012Q001D2Q01001216001200293Q0006570112001E2Q01000100040F012Q001E2Q010012160012002A4Q00FC0010001200020006570110002B2Q01000100040F012Q002B2Q01000ED30019002A2Q01000E00040F012Q002A2Q012Q004D0010000E4Q0046011100083Q001216001200294Q00E7001300014Q00FC0010001300020006570110002B2Q01000100040F012Q002B2Q012Q0062001000103Q00069A011000572Q013Q00040F012Q00572Q012Q0046011100033Q0012AC0012002B6Q001300053Q00122Q0014002C3Q00202Q00150006000B00122Q0016002D3Q00202Q00170006001300122Q0018002E6Q0012001200184Q0011000200014Q0011000F3Q00122Q0012002F3Q00202Q00120012002100202Q00130010001B00122Q001400203Q00202Q00140014002100122Q001500043Q00122Q001600113Q00122Q001700306Q0014001700024Q0013001300144Q0012000200024Q001300103Q00202Q0013001300314Q001400026Q0011001400014Q0011000B6Q0011000100024Q000F00113Q00062Q000F00942Q013Q00040F012Q00942Q010020E30011000F001B0020E300120010001B2Q00320111001100120020E300110011001F002695001100942Q01003200040F012Q00942Q012Q00E7000900013Q0020E300110010001B00105D01040033001100040F012Q00952Q0100040F012Q00942Q010020E30011000F001B2Q005B00110011000800202Q00110011001F4Q001200033Q00122Q0013002B6Q001400053Q00122Q001500343Q00202Q00160006000B00122Q0017002D3Q00202Q00180006001300122Q001900356Q001A00073Q00122Q001B00363Q00122Q001C001C3Q00202Q001C001C00374Q001D00116Q001C0002000200122Q001D00386Q00130013001D4Q00120002000100262Q001100772Q01003900040F012Q00772Q010012880112000F3Q0020E30012001200100012160013001A4Q0033001200020001000ED3003000942Q01000E00040F012Q00942Q012Q00E7000900013Q00309300040033003A00040F012Q00952Q0100040F012Q00942Q01000ED3003B00842Q01001100040F012Q00842Q012Q004D001200073Q0020E300130006000B2Q009C011200020002000657011200842Q01000100040F012Q00842Q012Q004D001200114Q003A011300086Q001400023Q00122Q001500396Q00120015000100044Q00942Q012Q004D0012000F3Q00120A0113002F3Q00202Q00130013002100202Q00140008003C00202Q00150008003D00202Q00150015003000202Q00160008003E4Q0013001600024Q001400103Q00202Q0014001400314Q001500026Q00120015000100122Q0012000F3Q00202Q00120012001000122Q0013001A6Q001200020001000406010B2Q002Q012Q0046010B00024Q0065010B00010002000657010B009A2Q01000100040F012Q009A2Q012Q000B012Q00013Q000657010900A42Q01000100040F012Q00A42Q012Q0046010B00033Q00121B010C003F6Q000B0002000100122Q000B000F3Q00202Q000B000B001000122Q000C00406Q000B000200016Q00014Q004D000B00053Q001266000C00413Q00202Q000D0006000B00202Q000E0006000C4Q000B000E000100302Q0004001800064Q000B8Q000C00033Q00122Q000D002B6Q000E00053Q00122Q000F00423Q0020E300100006000B001216001100434Q0087000D000D00112Q0033000C00020001001216000C001A3Q001216000D00283Q001216000E001A3Q000463000C00C72Q010012880110000F3Q0020E3001000100010001216001100444Q00330010000200012Q004D001000034Q0065011000010002000657011000C42Q01000100040F012Q00C42Q012Q004D001000063Q0020E30011000600132Q009C01100002000200069A011000C62Q013Q00040F012Q00C62Q012Q00E7000B00013Q00040F012Q00C72Q01000406010C00B72Q0100069A010B00CD2Q013Q00040F012Q00CD2Q010020E3000C000400260020E3000D000400332Q009E000C000A000D00040F012Q00DB2Q010020E3000C0004002600202C000C000A003A2Q0046010C00033Q001216000D00453Q0020E3000E00060013001216000F00464Q0087000D000D000F2Q0033000C00020001003093000400030004001288010C000F3Q0020E3000C000C0010001216000D00474Q0033000C000200012Q000B012Q00014Q0046010700024Q0065010700010002000657010700E02Q01000100040F012Q00E02Q012Q000B012Q00014Q004D000700124Q0030000800066Q000900046Q000A00016Q000B00056Q000C00026Q000D00036Q0007000D00016Q00017Q000D3Q0003093Q0069676E6F72654B6174030A3Q0063616B657072696E636503073Q00456E656D696573028Q00032C3Q0043616B65205072696E636520284B6174616B75726929206170617265636575212061746163616E646F3Q2E030A3Q00626F2Q73486569676874030A3Q00626F2Q73536B692Q6C73030A3Q0074772Q656E53702Q6564026Q00444003023Q006F7303053Q00636C6F636B026Q00394003113Q0043616B655072696E6365537061776E657202394Q004D00025Q0020E300020002000100069A0102000600013Q00040F012Q000600012Q00E700026Q00DA000200024Q004D000200014Q0013010300013Q001216000400024Q00230103000100012Q0013010400013Q001216000500034Q00230104000100012Q00FC0002000400022Q00D0000300023Q000ED3000400240001000300040F012Q002400012Q004D000300024Q0046010400024Q009C0103000200022Q0046010400013Q001216000500054Q00330004000200012Q004D000400034Q0046010500034Q004601066Q004D00075Q0020E30007000700062Q004D00085Q00207A0008000800074Q00095Q00202Q00090009000800122Q000A00096Q0004000A00014Q000400016Q000400023Q0012880103000A3Q00205000030003000B4Q0003000100024Q000400046Q000300030004000E2Q000C00360001000300040F012Q003600010012880103000A3Q00203E01030003000B4Q0003000100024Q000300046Q000300053Q00122Q0004000D6Q0003000200014Q000300053Q00122Q0004000D6Q000500016Q0003000500012Q00E700036Q00DA000300024Q000B012Q00019Q003Q00034Q00E73Q00014Q00DA3Q00024Q000B012Q00017Q00033Q0003043Q006661726D03083Q0075736551756573742Q0102084Q004D00025Q001216000300014Q001301043Q00010030930004000200032Q004601056Q0046010600014Q00EE0002000600012Q000B012Q00017Q00063Q0003053Q00626F6E657303083Q0075736551756573742Q012Q033Q006C6F6303073Q006861756E74656403063Q0066696C746572020F4Q000E01025Q00122Q000300016Q00043Q000300302Q0004000200034Q000500013Q00122Q000600056Q00050001000100105D0104000400050006B700053Q000100012Q004D3Q00013Q00104E0004000600054Q00058Q000600016Q0002000600016Q00013Q00013Q00013Q003Q01084Q004D00016Q0073000100013Q00267B000100050001000100040F012Q000500012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00073Q0003043Q0063616B6503083Q00757365517565737401002Q033Q006C6F6303083Q0063616B656C616E642Q033Q0070726503063Q0066696C74657202124Q00A001025Q00122Q000300016Q00043Q000400302Q0004000200034Q000500023Q00122Q000600053Q00122Q000700016Q00050002000100105D0104000400052Q004D000500013Q00105D0104000600050006B700053Q000100012Q004D3Q00023Q00104E0004000700054Q00058Q000600016Q0002000600016Q00013Q00013Q00013Q003Q01084Q004D00016Q0073000100013Q00267B000100050001000100040F012Q000500012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00073Q0003093Q0063616B65517565737403083Q0075736551756573742Q012Q033Q006C6F6303083Q0063616B656C616E6403043Q0063616B6503063Q0066696C74657202104Q00A001025Q00122Q000300016Q00043Q000300302Q0004000200034Q000500023Q00122Q000600053Q00122Q000700066Q00050002000100105D0104000400050006B700053Q000100012Q004D3Q00013Q00104E0004000700054Q00058Q000600016Q0002000600016Q00013Q00013Q00013Q003Q01084Q004D00016Q0073000100013Q00267B000100050001000100040F012Q000500012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00213Q0003073Q00456E656D696573028Q00030D3Q0020656E636F6E747261646F202803043Q006D61746803053Q00666C2Q6F7203053Q006D29207C20030A3Q00626F2Q73486569676874030A3Q00626F2Q73536B692Q6C73030A3Q0074772Q656E53702Q6564026Q00444003063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03043Q004E616D6503063Q00737472696E6703043Q0066696E64026Q00F03F03083Q00506F736974696F6E03093Q004D61676E6974756465026Q005940025Q00C0624003093Q00696E646F206174652003023Q00202803073Q002073747564732903073Q00566563746F72332Q033Q006E6577026Q004E4003093Q00706572746F20646520031C3Q002C20616775617264616E646F20656C652061706172656365723Q2E03043Q007461736B03043Q0077616974026Q00F83F04834Q001000048Q00058Q000600013Q00122Q000700016Q0006000100012Q00FC0004000600022Q00D0000500043Q000ED3000200270001000500040F012Q002700012Q004D000500014Q0046010600044Q00B20005000200062Q0046010700034Q0046010800013Q001216000900033Q001288010A00043Q0020E3000A000A000500068E000B00140001000600040F012Q00140001001216000B00024Q009C010A00020002001288000B00066Q000C00026Q000C000100024Q00080008000C4Q0007000200014Q000700036Q000800056Q000900026Q000A00043Q00202Q000A000A00072Q004D000B00043Q00207A000B000B00084Q000C00043Q00202Q000C000C000900122Q000D000A6Q0007000D00014Q000700016Q000700023Q0012880105000B4Q004D000600053Q00208D00060006000C2Q00DE000600074Q003501053Q000700040F012Q007E000100208D000A0009000D001216000C000E4Q00FC000A000C000200069A010A007E00013Q00040F012Q007E00012Q004D000A00063Q0020E3000B0009000F2Q009C010A00020002001288010B000B4Q0046010C6Q00B2000B0002000D00040F012Q007C0001001288011000103Q0020180110001000114Q0011000A6Q0012000F3Q00122Q001300126Q001400016Q00100014000200062Q0010007C00013Q00040F012Q007C00012Q004D001000074Q0046011100094Q009C01100002000200069A0110007C00013Q00040F012Q007C00010020E30011001000130020E3001100110014000ED30015007C0001001100040F012Q007C00012Q004D001100084Q006501110001000200069A0111005500013Q00040F012Q005500010020E30012001100130020E30013001000132Q00320112001200130020E3001200120014000657011200560001000100040F012Q00560001001216001200023Q000ED3001600700001001200040F012Q007000012Q0046011300033Q001213001400173Q00202Q00150009000F00122Q001600183Q00122Q001700043Q00202Q0017001700054Q001800126Q00170002000200122Q001800196Q0014001400184Q0013000200012Q004D001300093Q0020DB00140010001300122Q0015001A3Q00202Q00150015001B00122Q001600023Q00122Q0017001C3Q00122Q001800026Q0015001800024Q0014001400154Q001500023Q00122Q0016001C4Q00EE00130016000100040F012Q007A00012Q0046011300033Q0012160014001D3Q0020E300150009000F0012160016001E4Q00870014001400162Q00330013000200010012880113001F3Q0020E3001300130020001216001400214Q00330013000200012Q00E7001300014Q00DA001300023Q00062B000B00390001000200040F012Q0039000100062B0005002D0001000200040F012Q002D00012Q00E700056Q00DA000500024Q000B012Q00017Q001B3Q00026Q000840031F3Q00456C6974652048756E74657220736F20657869737465206E6F20536561203303043Q007461736B03043Q0077616974027Q004003063Q00646961626C6F03053Q00757262616E03073Q006465616E64726503053Q00456C69746503023Q006F7303053Q00636C6F636B026Q002840031D3Q00616775617264616E646F206F20656C69746520737061776E61723Q2E026Q00F83F030B3Q00656C69746568756E746572030E3Q00636173746C656F6E74686573656103063Q00636173746C65030E3Q006F20456C6974652048756E746572031D3Q0066616C616E646F20636F6D206F20456C6974652048756E7465723Q2E030B3Q00456C69746548756E74657203183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C2Q033Q007965732Q033Q0073696D03063Q00612Q6365707403073Q0061636569746172026Q000440025D4Q004D00026Q00610102000100012Q004D000200013Q00267B0002000D0001000100040F012Q000D00012Q0046010200013Q00121B010300026Q00020002000100122Q000200033Q00202Q00020002000400122Q000300056Q0002000200016Q00014Q004D000200024Q0013010300033Q001216000400063Q001216000500073Q001216000600084Q0023010300030001001216000400094Q004601056Q0046010600014Q00FC00020006000200069A0102001A00013Q00040F012Q001A00012Q000B012Q00013Q0012880102000A3Q00201F00020002000B4Q0002000100024Q000300036Q00020002000300262Q000200290001000C00040F012Q002900012Q0046010200013Q00121B0103000D6Q00020002000100122Q000200033Q00202Q00020002000400122Q0003000E6Q0002000200016Q00014Q004D000200044Q0013010300013Q0012160004000F4Q00230103000100012Q0013010400023Q001216000500103Q001216000600114Q00230104000200012Q004601056Q0046010600013Q001216000700124Q00FC00020007000200069A0102003B00013Q00040F012Q003B00012Q004601036Q00650103000100020006570103003C0001000100040F012Q003C00012Q000B012Q00014Q0046010300013Q001216000400134Q00330003000200010012880103000A3Q0020E300030003000B2Q00650103000100022Q00B8000300034Q004D000300053Q001216000400144Q00330003000200012Q004D000300063Q00208D000400020015001216000600164Q00A1010400064Q00FA00033Q000100122Q000300033Q00202Q00030003000400122Q0004000E6Q0003000200014Q000300076Q000400043Q00122Q000500173Q00122Q000600183Q00122Q000700193Q0012160008001A4Q00230104000400012Q00E7000500014Q00EE000300050001001288010300033Q0020E30003000300040012160004001B4Q00330003000200012Q000B012Q00017Q00013Q00026Q00344003104Q004D00036Q004601045Q001216000500013Q0006B700063Q000100022Q004D3Q00014Q0046012Q00013Q0006B700070001000100072Q004D3Q00014Q0046012Q00014Q004D3Q00024Q0046012Q00024Q004D3Q00034Q004D3Q00044Q004D3Q00054Q00EE0003000700012Q000B012Q00013Q00023Q00023Q0003073Q00456E656D696573029Q000D4Q004D8Q004D000100014Q0013010200013Q001216000300014Q00230102000100012Q00FC3Q000200022Q00D07Q000EA70102000A00013Q00040F012Q000A00012Q0011017Q00E73Q00014Q00DA3Q00024Q000B012Q00017Q000A3Q0003073Q00456E656D696573028Q0003023Q00202803043Q006D61746803053Q00666C2Q6F7203053Q006D29207C20030A3Q00626F2Q73486569676874030A3Q00626F2Q73536B692Q6C73030A3Q0074772Q656E53702Q6564026Q00444002274Q004D00026Q004D000300014Q0013010400013Q001216000500014Q00230104000100012Q00FC0002000400022Q00D0000300023Q0026810103000A0001000200040F012Q000A00012Q000B012Q00014Q004D000300024Q0046010400024Q00B20003000200042Q0046010500014Q004D000600033Q001216000700033Q001288010800043Q0020E300080008000500068E000900150001000400040F012Q00150001001216000900024Q009C010800020002001288000900066Q000A00046Q000A000100024Q00060006000A4Q0005000200014Q000500056Q000600036Q00078Q000800063Q00202Q0008000800072Q004D000900063Q0020E30009000900082Q004D000A00063Q0020E3000A000A0009001216000B000A4Q00EE0005000B00012Q000B012Q00017Q000A3Q0003063Q0069706169727303093Q0043686172616374657203083Q004261636B7061636B030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C03043Q004E616D6503063Q00737472696E6703043Q0066696E64026Q00F03F012F3Q0012882Q0100014Q0013010200024Q004D00035Q0020E30003000300022Q004D00045Q0020E30004000400032Q00230102000200012Q00B200010002000300040F012Q002A000100069A0105002A00013Q00040F012Q002A0001001288010600013Q00208D0007000500042Q00DE000700084Q003501063Q000800040F012Q0028000100208D000B000A0005001216000D00064Q00FC000B000D000200069A010B002800013Q00040F012Q002800012Q004D000B00013Q0020E3000C000A00072Q009C010B00020002001288010C00014Q0046010D6Q00B2000C0002000E00040F012Q00260001001288011100083Q0020180111001100094Q0012000B6Q001300103Q00122Q0014000A6Q001500016Q00110015000200062Q0011002600013Q00040F012Q002600012Q00DA000A00023Q00062B000C001C0001000200040F012Q001C000100062B000600100001000200040F012Q0010000100062B000100090001000200040F012Q000900012Q0062000100014Q00DA000100024Q000B012Q00017Q00013Q0003053Q007063612Q6C010C4Q004D00016Q00652Q010001000200069A2Q01000B00013Q00040F012Q000B000100069A012Q000B00013Q00040F012Q000B0001001288010200013Q0006B700033Q000100022Q0046012Q00014Q0046017Q00330002000200012Q000B012Q00013Q00013Q00013Q0003093Q004571756970542Q6F6C00054Q00927Q00206Q00014Q000200018Q000200016Q00017Q000D3Q0003053Q007063612Q6C028Q0003063Q006970616972732Q01030B3Q004765744368696C6472656E2Q033Q00497341030F3Q0050726F78696D69747950726F6D707403133Q006669726570726F78696D69747970726F6D7074030D3Q00436C69636B4465746563746F7203113Q0066697265636C69636B6465746563746F7203103Q00546F7563685472616E736D692Q74657203113Q0066697265746F756368696E746572657374026Q00F03F035B3Q001288010300013Q0006B700043Q000100022Q0046017Q0046012Q00014Q00B200030002000400069A0103000900013Q00040F012Q000900010006570104000B0001000100040F012Q000B0001001216000500024Q00DA000500023Q001216000500024Q001301066Q004D00076Q00650107000100020006B700080001000100022Q0046012Q00024Q004D3Q00013Q001288010900034Q0046010A00044Q00B200090002000B00040F012Q005700012Q0073000E0006000D000657010E00560001000100040F012Q005600012Q0046010E00084Q0046010F000D4Q009C010E0002000200069A010E005600013Q00040F012Q0056000100202C0006000D00042Q0021010E5Q00122Q000F00033Q00202Q0010000D00054Q001000116Q000F3Q001100044Q0051000100208D001400130006001216001600074Q00FC00140016000200069A0114003300013Q00040F012Q00330001001288011400083Q00069A0114003300013Q00040F012Q00330001001288011400013Q0012B3011500086Q001600136Q0014001600014Q000E00013Q00044Q0051000100208D001400130006001216001600094Q00FC00140016000200069A0114004100013Q00040F012Q004100010012880114000A3Q00069A0114004100013Q00040F012Q00410001001288011400013Q0012B30115000A6Q001600136Q0014001600014Q000E00013Q00044Q0051000100208D0014001300060012160016000B4Q00FC00140016000200069A0114005100013Q00040F012Q005100010012880114000C3Q00069A0114005100013Q00040F012Q0051000100069A0107005100013Q00040F012Q00510001001288011400013Q0006B700150002000100022Q0046012Q00074Q0046012Q000D4Q00330014000200012Q00E7000E00013Q00062B000F00250001000200040F012Q0025000100069A010E005600013Q00040F012Q005600010020AC01050005000D2Q000F000C5Q00062B000900160001000200040F012Q001600012Q00DA000500024Q000B012Q00013Q00033Q00043Q0003093Q00776F726B737061636503153Q0047657450617274426F756E6473496E526164697573030D3Q004F7665726C6170506172616D732Q033Q006E6577000A3Q001288012Q00013Q00208D5Q00022Q004D00026Q004D000300013Q001288010400033Q0020E30004000400042Q0077010400014Q003E8Q0091017Q000B012Q00017Q00073Q0003043Q004E616D6503063Q00506172656E74034Q0003063Q0069706169727303063Q00737472696E6703043Q0066696E64026Q00F03F012F4Q004D00015Q0006572Q0100050001000100040F012Q000500012Q00E7000100014Q00DA000100024Q004D000100013Q0020E300023Q00012Q009C2Q01000200020020E300023Q000200069A0102001100013Q00040F012Q001100012Q004D000200013Q0020E300033Q00020020E30003000300012Q009C010200020002000657010200120001000100040F012Q00120001001216000200033Q001288010300044Q004D00046Q00B200030002000500040F012Q002A0001001288010800053Q0020530008000800064Q000900016Q000A00073Q00122Q000B00076Q000C00016Q0008000C000200062Q000800280001000100040F012Q00280001001288010800053Q0020180108000800064Q000900026Q000A00073Q00122Q000B00076Q000C00016Q0008000C000200062Q0008002A00013Q00040F012Q002A00012Q00E7000800014Q00DA000800023Q00062B000300160001000200040F012Q001600012Q00E700036Q00DA000300024Q000B012Q00017Q00063Q0003113Q0066697265746F756368696E746572657374028Q0003043Q007461736B03043Q0077616974029A5Q99A93F026Q00F03F000F3Q001288012Q00014Q004D00016Q004D000200013Q001216000300024Q00EE3Q00030001001288012Q00033Q0020E35Q0004001216000100054Q00333Q00020001001288012Q00014Q004D00016Q004D000200013Q001216000300064Q00EE3Q000300012Q000B012Q00017Q00013Q00026Q003E4002144Q004D00026Q004601035Q001216000400013Q0006B700053Q000100022Q004D3Q00014Q0046016Q0006B7000600010001000B2Q004D3Q00024Q0046012Q00014Q004D3Q00034Q004D3Q00044Q0046017Q004D3Q00054Q004D3Q00064Q004D3Q00074Q004D3Q00014Q004D3Q00084Q004D3Q00094Q00EE0002000600012Q000B012Q00013Q00028Q00054Q00F59Q00000100019Q0000016Q00028Q00017Q001D3Q002Q033Q0073656103133Q00736F2066756E63696F6E61206E6F205365612003043Q006974656D03153Q00766F6365206E616F2074656D206F206974656D3A2003083Q006974656D4E616D6503063Q006970616972732Q033Q006C6F63030A3Q006E616F2061636865692003053Q00706C61636503123Q00206E61206C6973746120646520696C686173030A3Q00696E646F2070617261202Q033Q003Q2E03063Q00434672616D652Q033Q006E657703073Q00566563746F7233028Q00025Q0080514003073Q00747053702Q656403043Q007461736B03043Q0077616974026Q00F03F026Q00E03F03063Q00726164697573026Q00794003083Q0070612Q7465726E7303083Q006163696F6E65692003243Q00206F626A65746F2873292E205365206F20626F2Q73206E616F2061706172656365753A2003043Q0068696E74031E3Q006E616F206163686569206F206C6F63616C20646520696E766F6361722E2002864Q004D00026Q00610102000100012Q004D000200013Q0020E300020002000100069A0102001600013Q00040F012Q001600012Q004D000200024Q004D000300013Q0020E30003000300010006AD000200160001000300040F012Q001600012Q0046010200013Q001211000300026Q000400013Q00202Q0004000400014Q0003000300044Q0002000200014Q000200036Q000300046Q00048Q0002000400016Q00014Q004D000200054Q004D000300013Q0020E30003000300032Q009C010200020002000657010200270001000100040F012Q002700012Q0046010300013Q001211000400046Q000500013Q00202Q0005000500054Q0004000400054Q0003000200014Q000300036Q000400046Q00058Q0003000500016Q00014Q0062000300033Q001215010400066Q000500013Q00202Q0005000500074Q00040002000600044Q00330001000657010300330001000100040F012Q003300012Q004D000900064Q0046010A00084Q009C0109000200022Q0046010300093Q00062B0004002D0001000200040F012Q002D0001000657010300430001000100040F012Q004300012Q0046010400013Q001247010500086Q000600013Q00202Q00060006000900122Q0007000A6Q0005000500074Q0004000200014Q000400036Q000500046Q00068Q0004000600012Q000B012Q00014Q0046010400013Q0012810005000B6Q000600013Q00202Q00060006000900122Q0007000C6Q0005000500074Q0004000200014Q000400073Q00122Q0005000D3Q00202Q00050005000E00122Q0006000F3Q0020E300060006000E001216000700103Q001216000800113Q001216000900104Q00FC0006000900022Q00330106000300062Q009C0105000200022Q004D000600083Q0020E30006000600122Q004601076Q00FC0004000700020006570104005C0001000100040F012Q005C00012Q000B012Q00013Q001288010400133Q0020E3000400040014001216000500154Q00330004000200012Q004D000400094Q0046010500024Q0033000400020001001288010400133Q0020E3000400040014001216000500164Q00330004000200012Q004D0004000A4Q0046010500034Q004D000600013Q0020E30006000600170006570106006E0001000100040F012Q006E0001001216000600184Q004D000700013Q0020E30007000700192Q00FC0004000700022Q0046010500013Q000ED30010007C0001000400040F012Q007C00010012160006001A4Q0046010700043Q0012160008001B4Q004D000900013Q0020E300090009001C2Q0087000600060009000657010600800001000100040F012Q008000010012160006001D4Q004D000700013Q0020E300070007001C2Q00870006000600072Q00330005000200012Q00ED000500036Q000600046Q00078Q0005000700016Q00017Q00013Q0003043Q007061647300044Q004D7Q0020E35Q00012Q00DA3Q00024Q000B012Q00017Q00183Q00026Q00084003143Q00736F2066756E63696F6E61206E6F20536561203303043Q0070616473030E3Q00636173746C656F6E74686573656103063Q00636173746C65031D3Q006E616F206163686569206F20436173746C65206F6E2074686520536561031C3Q00696E646F20616F20436173746C65206F6E20746865205365613Q2E03063Q00434672616D652Q033Q006E657703073Q00566563746F7233028Q00025Q0080514003073Q00747053702Q656403043Q007461736B03043Q0077616974026Q00F03F025Q00C082402Q033Q0070616403063Q0062752Q746F6E03043Q0068616B6903043Q006175726103053Q00706C617465030A3Q00746F7175656920656D2003313Q00207061642873292E204361646120706164207072656369736120646120636F72206465204175726120636F2Q726574612E024E4Q004D00026Q00610102000100012Q004D000200013Q00267B0002000D0001000100040F012Q000D00012Q0046010200013Q001286010300026Q0002000200014Q000200023Q00122Q000300036Q00048Q0002000400016Q00014Q004D000200033Q001216000300044Q009C010200020002000657010200150001000100040F012Q001500012Q004D000200033Q001216000300054Q009C0102000200020006570102001F0001000100040F012Q001F00012Q0046010300013Q001286010400066Q0003000200014Q000300023Q00122Q000400036Q00058Q0003000500016Q00014Q0046010300013Q001290000400076Q0003000200014Q000300043Q00122Q000400083Q00202Q00040004000900122Q0005000A3Q00202Q00050005000900122Q0006000B3Q00122Q0007000C3Q00122Q0008000B6Q0005000800024Q0005000200054Q0004000200024Q000500053Q00202Q00050005000D4Q00068Q00030006000200062Q000300340001000100040F012Q003400012Q000B012Q00013Q0012880103000E3Q00206D00030003000F00122Q000400106Q0003000200014Q000300066Q000400023Q00122Q000500116Q000600053Q00122Q000700123Q00122Q000800133Q00122Q000900143Q001216000A00153Q001216000B00164Q00230106000500012Q00FC0003000600022Q0046010400013Q001216000500174Q0046010600033Q001216000700184Q00870005000500072Q00330004000200012Q004D000400023Q001216000500034Q00E700066Q00EE0004000600012Q000B012Q00017Q000C3Q0003093Q006461726B6265617264030B3Q004261726261204E6567726103083Q00686F7044656C6179026Q00F03F026Q00F0BF03073Q00456E656D696573028Q0003333Q004261726261204E65677261206E616F206573746120617175692C2074726F63616E646F206465207365727669646F7220656D2003013Q007303043Q007461736B03043Q0077616974026Q00244002394Q004D00026Q0013010300013Q001216000400014Q0023010300010001001216000400024Q004601056Q0046010600014Q00FC00020006000200069A0102000B00013Q00040F012Q000B00012Q000B012Q00014Q004D000200013Q0020E3000200020003001216000300043Q001216000400053Q0004630002002C00012Q004601066Q0065010600010002000657010600150001000100040F012Q001500012Q000B012Q00014Q004D000600024Q0013010700013Q001216000800014Q00230107000100012Q0013010800013Q001216000900064Q00230108000100012Q00FC0006000800022Q00D0000600063Q000ED3000700210001000600040F012Q002100012Q000B012Q00014Q0046010600013Q001216000700084Q0046010800053Q001216000900094Q00870007000700092Q00330006000200010012880106000A3Q0020E300060006000B001216000700044Q00330006000200010004060102001000012Q004601026Q006501020001000200069A0102003400013Q00040F012Q003400012Q004D000200033Q0006B700033Q000100012Q0046012Q00014Q00330002000200010012880102000A3Q0020E300020002000B0012160003000C4Q00330002000200012Q000B012Q00013Q00017Q0001044Q004D00016Q004601026Q00330001000200012Q000B012Q00017Q00183Q0003093Q006C657669617468616E03093Q0053656142656173747303063Q0069706169727303063Q00737472696E6703043Q0066696E642Q033Q006D646C03043Q004E616D6503073Q007365676D656E74026Q00F03F03053Q007461626C6503063Q00696E73657274028Q0003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030B3Q004765744368696C6472656E030E3Q0047657444657363656E64616E74732Q033Q0049734103053Q004D6F64656C03083Q00426173655061727403153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403063Q004865616C746803043Q00706172742Q033Q0068756D00724Q004D8Q00132Q0100013Q001216000200014Q00232Q01000100012Q0013010200013Q001216000300024Q00230102000100012Q00FC3Q000200022Q004100015Q00122Q000200036Q00038Q00020002000400044Q001E0001001288010700043Q0020E30007000700052Q004D000800013Q0020E30009000600060020E30009000900072Q009C010800020002001216000900083Q001216000A00094Q00E7000B00014Q00FC0007000B000200069A0107001E00013Q00040F012Q001E00010012880107000A3Q0020E300070007000B2Q0046010800014Q0046010900064Q00EE00070009000100062B0002000D0001000200040F012Q000D00012Q00D0000200013Q0026810102006C0001000C00040F012Q006C00010012880102000D3Q00208D00020002000E001216000400024Q00FC00020004000200069A0102006C00013Q00040F012Q006C0001001288010300033Q00208D00040002000F2Q00DE000400054Q003501033Q000500040F012Q006A0001001288010800043Q0020190008000800054Q000900013Q00202Q000A000700074Q00090002000200122Q000A00013Q00122Q000B00096Q000C00016Q0008000C000200062Q0008006A00013Q00040F012Q006A0001001288010800033Q00208D0009000700102Q00DE0009000A4Q003501083Q000A00040F012Q0068000100208D000D000C0011001216000F00124Q00FC000D000F0002000657010D00480001000100040F012Q0048000100208D000D000C0011001216000F00134Q00FC000D000F000200069A010D006800013Q00040F012Q00680001001288010D00043Q002019000D000D00054Q000E00013Q00202Q000F000C00074Q000E0002000200122Q000F00083Q00122Q001000096Q001100016Q000D0011000200062Q000D006800013Q00040F012Q006800012Q004D000D00024Q0046010E000C4Q009C010D0002000200208D000E000C0014001216001000154Q00FC000E0010000200069A010D006800013Q00040F012Q0068000100069A010E006000013Q00040F012Q006000010020E3000F000E0016000ED3000C00680001000F00040F012Q00680001001288010F000A3Q002028000F000F000B4Q001000016Q00113Q000300102Q00110006000C00102Q00110017000D00102Q00110018000E4Q000F0011000100062B0008003E0001000200040F012Q003E000100062B0003002E0001000200040F012Q002E00012Q00D0000200013Q000ED3000C00700001000200040F012Q007000012Q00DA000100024Q00DA3Q00024Q000B012Q00017Q00083Q0003063Q006970616972732Q033Q006B657903083Q007365676D656E747303053Q006E616D657303023Q00657603053Q006C6162656C03053Q007461626C6503063Q00696E7365727400274Q0013016Q0012882Q0100014Q004D00026Q00B200010002000300040F012Q002300012Q004D000600013Q0020E30007000500022Q007300060006000700069A0106002300013Q00040F012Q002300012Q0062000600063Q0020E300070005000300069A0107001200013Q00040F012Q001200012Q004D000700024Q00650107000100022Q0046010600073Q00040F012Q001600012Q004D000700033Q0020E30008000500042Q009C0107000200022Q0046010600073Q001288010700014Q0046010800064Q00B200070002000900040F012Q002100010020E3000C0005000600105D010B0005000C001288010C00073Q0020E3000C000C00082Q0046010D6Q0046010E000B4Q00EE000C000E000100062B0007001A0001000200040F012Q001A000100062B000100050001000200040F012Q000500012Q00DA3Q00024Q000B012Q00017Q00013Q00029Q00094Q004D8Q0065012Q000100022Q00D07Q000EA72Q01000600013Q00040F012Q000600012Q0011017Q00E73Q00014Q00DA3Q00024Q000B012Q00017Q000A3Q00028Q0003023Q00657603023Q00202803043Q006D61746803053Q00666C2Q6F7203053Q006D29207C2003093Q0073656148656967687403093Q00736561536B692Q6C7303083Q0073656153702Q6564026Q003E4002234Q004D00026Q00650102000100022Q00D0000300023Q002681010300060001000100040F012Q000600012Q000B012Q00014Q004D000300014Q0046010400024Q00B20003000200042Q0046010500013Q0020E3000600030002001216000700033Q001288010800043Q0020E300080008000500068E000900110001000400040F012Q00110001001216000900014Q009C010800020002001288000900066Q000A00026Q000A000100024Q00060006000A4Q0005000200014Q000500036Q000600036Q00078Q000800043Q00202Q0008000800072Q004D000900043Q0020E30009000900082Q004D000A00043Q0020E3000A000A0009001216000B000A4Q00EE0005000B00012Q000B012Q00017Q00023Q0003063Q006970616972732Q033Q006B657900103Q001288012Q00014Q004D00016Q00B23Q0002000200040F012Q000B00012Q004D000500013Q0020E30006000400022Q007300050005000600069A0105000B00013Q00040F012Q000B00012Q00E7000500014Q00DA000500023Q00062B3Q00040001000200040F012Q000400012Q00E78Q00DA3Q00024Q000B012Q00017Q000A3Q0003083Q00746F737472696E6703063Q00737472696E6703053Q006D61746368030B3Q005E285B5E252D5D2B29252D03053Q006C6F77657203043Q0067737562030C3Q0025732A667275697425732A24034Q0003063Q005B5E612D7A5D027Q0040012D3Q0012882Q0100014Q004601026Q009C2Q01000200022Q0046012Q00013Q0012882Q0100023Q0020E30001000100032Q004601025Q001216000300044Q00FC0001000300020006572Q01000C0001000100040F012Q000C00012Q00462Q015Q001288010200023Q0020E30002000200052Q0046010300014Q009C010200020002001288010300023Q0020E30003000300062Q0046010400023Q001216000500073Q001216000600084Q00FC0003000600022Q0046010200033Q001288010300023Q0020E30003000300062Q0046010400023Q001216000500093Q001216000600084Q00FC0003000600022Q0046010200034Q00D0000300023Q0026950003002B0001000A00040F012Q002B0001001288010300023Q0020A401030003000600122Q000400023Q00202Q0004000400054Q00058Q00040002000200122Q000500093Q00122Q000600086Q0003000600024Q000200034Q00DA000200024Q000B012Q00017Q00123Q00030C3Q00476574412Q74726962757465030C3Q004F726967696E616C4E616D6503093Q0046727569744E616D6503043Q004E616D6503083Q00746F737472696E6703063Q00737472696E6703043Q006773756203043Q005E25732B034Q0003043Q0025732B2403053Q006C6F77657203053Q00667275697403063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q0049734103053Q004D6F64656C03053Q00467275697403063Q0048616E646C6501393Q00208D00013Q0001001216000300024Q00FC0001000300020006572Q01000B0001000100040F012Q000B000100208D00013Q0001001216000300034Q00FC0001000300020006572Q01000B0001000100040F012Q000B00010020E300013Q0004001288010200054Q000C000300016Q0002000200024Q000100023Q00122Q000200063Q00202Q0002000200074Q000300013Q00122Q000400083Q00122Q000500096Q0002000500024Q000100023Q00122Q000200063Q00202Q0002000200074Q000300013Q00122Q0004000A3Q00122Q000500096Q0002000500024Q000100023Q00122Q000200063Q00202Q00020002000B4Q000300016Q00020002000200262Q000200370001000C00040F012Q003700010012880102000D3Q00208D00033Q000E2Q00DE000300044Q003501023Q000400040F012Q0035000100208D00070006000F001216000900104Q00FC00070009000200069A0107003500013Q00040F012Q003500010020E300070006000400267B000700350001001100040F012Q003500010020E300070006000400267B000700350001001200040F012Q003500010020E300010006000400040F012Q0037000100062B000200280001000200040F012Q002800012Q00DA000100024Q000B012Q00017Q00173Q0003063Q0069706169727303093Q00776F726B7370616365030B3Q004765744368696C6472656E03063Q00737472696E6703053Q006D6174636803053Q006C6F77657203043Q004E616D65030D3Q005E667275697425732A25642B24002Q033Q0049734103043Q00542Q6F6C03053Q004D6F64656C03043Q0066696E6403053Q004672756974030E3Q0046696E6446697273744368696C6403063Q0048616E646C6503163Q0046696E6446697273744368696C64576869636849734103083Q00426173655061727403053Q007461626C6503063Q00696E736572742Q033Q006F626A03043Q007061727403043Q006E616D6500404Q007E7Q00122Q000100013Q00122Q000200023Q00202Q0002000200034Q000200036Q00013Q000300044Q003C0001001288010600043Q0020E3000600060005001288010700043Q0020E30007000700060020E30008000500072Q009C010700020002001216000800084Q00FC000600080002002681010600120001000900040F012Q001200012Q001101066Q00E7000600013Q0006570106003C0001000100040F012Q003C000100208D00070005000A0012160009000B4Q00FC0007000900020006570107001F0001000100040F012Q001F000100208D00070005000A0012160009000C4Q00FC00070009000200069A0107003C00013Q00040F012Q003C0001001288010700043Q0020E300070007000D0020E30008000500070012160009000E4Q00FC00070009000200069A0107003C00013Q00040F012Q003C000100208D00070005000F001216000900104Q00FC0007000900020006570107002F0001000100040F012Q002F000100208D000700050011001216000900124Q00E7000A00014Q00FC0007000A000200069A0107003C00013Q00040F012Q003C0001001288010800133Q0020240008000800144Q00098Q000A3Q000300102Q000A0015000500102Q000A001600074Q000B8Q000C00056Q000B0002000200102Q000A0017000B4Q0008000A000100062B000100070001000200040F012Q000700012Q00DA3Q00024Q000B012Q00017Q00023Q0003113Q0066697265746F756368696E74657265737403053Q007063612Q6C010D4Q004D00016Q00652Q010001000200069A2Q01000C00013Q00040F012Q000C0001001288010200013Q00069A0102000C00013Q00040F012Q000C0001001288010200023Q0006B700033Q000100022Q0046012Q00014Q0046017Q00330002000200012Q000B012Q00013Q00013Q00063Q0003113Q0066697265746F756368696E746572657374028Q0003043Q007461736B03043Q0077616974029A5Q99A93F026Q00F03F000F3Q001288012Q00014Q004D00016Q004D000200013Q001216000300024Q00EE3Q00030001001288012Q00033Q0020E35Q0004001216000100054Q00333Q00020001001288012Q00014Q004D00016Q004D000200013Q001216000300064Q00EE3Q000300012Q000B012Q00017Q00033Q002Q033Q00696E760003043Q006261736501114Q00FB00018Q00028Q0001000200024Q000200013Q00202Q0002000200014Q00020002000100262Q0002000E0001000200040F012Q000E00012Q004D000200013Q0020E30002000200032Q00730002000200010026810102000E0001000200040F012Q000E00012Q001101026Q00E7000200014Q00DA000200024Q000B012Q00017Q000D3Q0003053Q0070616972732Q033Q00696E7603053Q007461626C6503063Q00696E7365727403043Q006261736503043Q00736F727403043Q0054657874028Q0003213Q004D696E6861732066727574617320646574656374616461733A206E656E68756D61031A3Q004D696E68617320667275746173206465746563746164617320282Q033Q00293A2003063Q00636F6E63617403023Q002C2000384Q004D7Q000657012Q00040001000100040F012Q000400012Q000B012Q00014Q0013016Q0012152Q0100016Q000200013Q00202Q0002000200024Q00010002000300044Q000F0001001288010600033Q0020E30006000600042Q004601076Q0046010800054Q00EE00060008000100062B0001000A0001000200040F012Q000A00010012882Q0100014Q004D000200013Q0020E30002000200052Q00B200010002000300040F012Q002000012Q004D000600013Q0020E30006000600022Q0073000600060004000657010600200001000100040F012Q00200001001288010600033Q0020E30006000600042Q004601076Q0046010800054Q00EE00060008000100062B000100160001000200040F012Q001600010012882Q0100033Q0020E30001000100062Q004601026Q00330001000200012Q004D00016Q00D000025Q0026810102002D0001000800040F012Q002D0001001216000200093Q000657010200360001000100040F012Q003600010012160002000A4Q00AB01035Q00122Q0004000B3Q00122Q000500033Q00202Q00050005000C4Q00065Q00122Q0007000D6Q0005000700024Q00020002000500105D2Q01000700022Q000B012Q00017Q000B3Q002Q033Q0049734103043Q00542Q6F6C030C3Q00476574412Q74726962757465030C3Q004F726967696E616C4E616D6500030E3Q0046696E6446697273744368696C6403053Q00467275697403063Q00737472696E6703043Q0066696E6403043Q004E616D6503103Q005E5B2561205D2B252D5B2561205D2B2401293Q00208D00013Q0001001216000300024Q00FC0001000300020006572Q0100070001000100040F012Q000700012Q00E700016Q00DA000100023Q00208D00013Q0003001216000300044Q00FC00010003000200267B0001000E0001000500040F012Q000E00012Q00E7000100014Q00DA000100023Q00208D00013Q0006001216000300074Q00FC00010003000200267B000100150001000500040F012Q001500012Q00E7000100014Q00DA000100023Q0012882Q0100083Q00203F2Q010001000900202Q00023Q000A00122Q000300076Q00010003000200262Q0001001E0001000500040F012Q001E00012Q00E7000100014Q00DA000100023Q0012882Q0100083Q00208400010001000900202Q00023Q000A00122Q0003000B6Q00010003000200262Q000100260001000500040F012Q002600012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00033Q00030C3Q00476574412Q74726962757465030C3Q004F726967696E616C4E616D6503043Q004E616D6501083Q00208D00013Q0001001216000300024Q00FC0001000300020006572Q0100060001000100040F012Q000600010020E300013Q00032Q00DA000100024Q000B012Q00017Q00063Q0003063Q0069706169727303083Q004261636B7061636B03093Q00436861726163746572030B3Q004765744368696C6472656E03053Q007461626C6503063Q00696E7365727400214Q00867Q00122Q000100016Q000200026Q00035Q00202Q0003000300024Q00045Q00202Q0004000400034Q0002000200012Q00B200010002000300040F012Q001D000100069A0105001D00013Q00040F012Q001D0001001288010600013Q00208D0007000500042Q00DE000700084Q003501063Q000800040F012Q001B00012Q004D000B00014Q0046010C000A4Q009C010B0002000200069A010B001B00013Q00040F012Q001B0001001288010B00053Q0020E3000B000B00062Q0046010C6Q0046010D000A4Q00EE000B000D000100062B000600110001000200040F012Q0011000100062B0001000A0001000200040F012Q000A00012Q00DA3Q00024Q000B012Q00017Q00033Q0003043Q006261736503063Q0069706169727303083Q00746F737472696E6700174Q004D8Q00132Q015Q00105D012Q00010001001297012Q00026Q000100016Q000100019Q00000200044Q001400012Q004D000500024Q0089010600046Q0005000200024Q00065Q00202Q0006000600014Q000700036Q000800056Q00070002000200122Q000800036Q000900056Q0008000200024Q00060007000800062B3Q00080001000200040F012Q000800012Q000B012Q00017Q000C3Q00030C3Q00676574496E76656E746F727903043Q007479706503053Q007461626C6503053Q00706169727303043Q004E616D6503083Q00746F737472696E6703043Q0054797065030A3Q00426C6F7820467275697403063Q00737472696E6703043Q0066696E6403023Q00252D2Q033Q00696E76002D4Q004D7Q001216000100014Q009C012Q000200020012882Q0100024Q004601026Q009C2Q01000200020026812Q01002A0001000300040F012Q002A00012Q00132Q015Q001288010200044Q004601036Q00B200020002000400040F012Q00260001001288010700024Q0046010800064Q009C010700020002002681010700260001000300040F012Q002600010020E300070006000500069A0107002600013Q00040F012Q00260001001288010700063Q0020E30008000600052Q009C0107000200020020E300080006000700267B000800220001000800040F012Q00220001001288010800093Q0020BF00080008000A4Q000900073Q00122Q000A000B6Q0008000A000200062Q0008002600013Q00040F012Q002600012Q004D000800014Q0046010900074Q009C0108000200022Q009E00010008000700062B0002000D0001000200040F012Q000D00012Q004D000200023Q00105D0102000C00012Q004D000100034Q00612Q01000100012Q000B012Q00017Q000C3Q0003223Q0072656D6F74652064652061726D617A656E6172206E616F20656E636F6E747261646F03063Q0069706169727303053Q007472696573028Q00026Q000840026Q00F03F030C3Q0061726D617A656E616E646F2003083Q00746F737472696E6703053Q007063612Q6C03043Q007461736B03043Q0077616974026Q33E33F01454Q004D00016Q00652Q01000100020006572Q0100090001000100040F012Q000900012Q004601025Q001216000300014Q00330002000200012Q00E700026Q00DA000200024Q00E700025Q001297010300026Q000400016Q000400016Q00033Q000500044Q003D00012Q004D000800024Q0046010900074Q009C0108000200022Q004D000900034Q0046010A00084Q009C0109000200020006570109003B0001000100040F012Q003B00012Q004D000900043Q0020E30009000900032Q00730009000900070006570109001D0001000100040F012Q001D0001001216000900043Q0026950009003B0001000500040F012Q003B00012Q004D000900043Q0020480109000900034Q000A00043Q00202Q000A000A00034Q000A000A000700062Q000A00270001000100040F012Q00270001001216000A00043Q0020AC010A000A00062Q009E00090007000A2Q004601095Q001216000A00073Q001288010B00084Q0046010C00084Q009C010B000200022Q0087000A000A000B2Q0033000900020001001288010900093Q0006B7000A3Q000100032Q0046012Q00014Q0046012Q00084Q0046012Q00074Q005E0109000200014Q000200013Q00122Q0009000A3Q00202Q00090009000B00122Q000A000C6Q0009000200012Q000F00086Q000F00065Q00062B0003000F0001000200040F012Q000F000100069A0102004300013Q00040F012Q004300012Q004D000300054Q00610103000100012Q00DA000200024Q000B012Q00013Q00013Q00023Q00030C3Q00496E766F6B65536572766572030A3Q0053746F7265467275697400084Q00C97Q00206Q000100122Q000200026Q000300016Q000400028Q00049Q008Q00017Q00093Q0003063Q0069706169727303073Q00736B692Q7065642Q033Q006F626A03023Q006F7303053Q00636C6F636B03043Q006E616D6503043Q007061727403083Q00506F736974696F6E03093Q004D61676E6974756465002E4Q004D8Q0065012Q00010002000657012Q00060001000100040F012Q000600012Q0062000100014Q00DA000100024Q0062000100023Q001297010300016Q000400016Q000400016Q00033Q000500044Q002800012Q004D000800023Q0020E30008000800020020E30009000700032Q007300080008000900069A0108001700013Q00040F012Q00170001001288010900043Q0020E30009000900052Q0065010900010002000639010900280001000800040F012Q002800012Q004D000900033Q0020E3000A000700062Q009C010900020002000657010900280001000100040F012Q002800010020E300090007000700206401090009000800202Q000A3Q00084Q00090009000A00202Q00090009000900062Q0002002500013Q00040F012Q00250001000676010900280001000200040F012Q002800012Q0046010A00074Q0046010200094Q00462Q01000A3Q00062B0003000C0001000200040F012Q000C00012Q0046010300014Q0046010400024Q0036000300034Q000B012Q00017Q00083Q0003053Q0066727569742Q033Q00686F7003073Q00736B692Q70656403053Q00747269657303093Q006E6F6E6553696E636500030B3Q006C61737452656672657368028Q00010F3Q00267B3Q00040001000100040F012Q00040001002681012Q000E0001000200040F012Q000E00012Q004D00016Q004D00026Q004D00036Q001301046Q001301055Q00309300030005000600105D01020004000500105D2Q01000300042Q004D00015Q0030930001000700082Q000B012Q00017Q00013Q0003063Q00697061697273000F3Q001288012Q00014Q004D00016Q00B23Q0002000200040F012Q000A00012Q004D000500014Q007300050005000400069A0105000A00013Q00040F012Q000A00012Q00E7000500014Q00DA000500023Q00062B3Q00040001000200040F012Q000400012Q00E78Q00DA3Q00024Q000B012Q00017Q00013Q002Q033Q00686F7000134Q004D8Q0065012Q0001000200069A012Q000600013Q00040F012Q000600012Q00E73Q00014Q00DA3Q00024Q004D3Q00013Q0020E35Q000100069A012Q001000013Q00040F012Q001000012Q004D3Q00024Q0065012Q00010002000657012Q00100001000100040F012Q001000012Q00E73Q00014Q00DA3Q00024Q00E78Q00DA3Q00024Q000B012Q00017Q00293Q0003063Q00696E697465642Q0103193Q00646574656374616E646F2073756173206672757461733Q2E03023Q006F7303053Q00636C6F636B030B3Q006C61737452656672657368026Q003E4003053Q0073746F726503093Q006E6F6E6553696E636503043Q006D6174682Q033Q006D6178028Q0003083Q00686F7044656C61792Q033Q00686F7003313Q006E656E68756D61206672757461206E6F766120617175692C2074726F63616E646F206465207365727669646F7220656D2003043Q006365696C03013Q0073031A3Q006E656E68756D61206672757461206E6F7661206E6F206D61706103043Q007461736B03043Q0077616974026Q00F03F0003093Q00696E646F206174652003043Q006E616D6503023Q00202803053Q00666C2Q6F7203023Q006D2903063Q00434672616D652Q033Q006E657703043Q007061727403083Q00506F736974696F6E03073Q00566563746F7233026Q000840030A3Q00667275697453702Q656403083Q00706567616E646F202Q033Q006F626A03063Q00506172656E74026Q001440026Q33D33F03073Q00736B692Q706564026Q004E4002CF4Q004D00025Q0020E30002000200010006570102000D0001000100040F012Q000D00012Q004D00025Q0030930002000100022Q0046010200013Q001216000300034Q00330002000200012Q004D000200014Q00610102000100012Q004D000200024Q0061010200010001001288010200043Q0020E30002000200052Q00650102000100022Q004D00035Q0020E30003000300062Q0032010200020003000ED30007001C0001000200040F012Q001C00012Q004D00025Q001288010300043Q0020E30003000300052Q006501030001000200105D0102000600032Q004D000200024Q00610102000100012Q004D000200034Q00B10002000100030006570102005D0001000100040F012Q005D00012Q004D000400043Q0020E300040004000800069A0104002700013Q00040F012Q002700012Q004D000400054Q0046010500014Q00330004000200012Q004D00046Q004D00055Q0020E30005000500090006570105002F0001000100040F012Q002F0001001288010500043Q0020E30005000500052Q006501050001000200105D0104000900050012880104000A3Q0020E300040004000B0012160005000C4Q004D000600043Q0020E300060006000D001288010700043Q0020E30007000700052Q00650107000100022Q004D00085Q0020E30008000800092Q00320107000700082Q00320106000600072Q00FC0004000600022Q004D000500043Q0020E300050005000E00069A0105005500013Q00040F012Q005500012Q0046010500013Q0012710006000F3Q00122Q0007000A3Q00202Q0007000700104Q000800046Q00070002000200122Q000800116Q0006000600084Q00050002000100262Q000400580001000C00040F012Q005800012Q004D000500064Q0046010600014Q00330005000200012Q004D00055Q001288010600043Q0020E30006000600052Q006501060001000200105D01050009000600040F012Q005800012Q0046010500013Q001216000600124Q0033000500020001001288010500133Q0020E3000500050014001216000600154Q00330005000200012Q000B012Q00014Q004D00045Q0030930004000900162Q0046010400013Q001213000500173Q00202Q00060002001800122Q000700193Q00122Q0008000A3Q00202Q00080008001A4Q000900036Q00080002000200122Q0009001B6Q0005000500094Q0004000200012Q004D000400073Q0012880105001C3Q0020E300050005001D0020E300060002001E0020E300060006001F001203000700203Q00202Q00070007001D00122Q0008000C3Q00122Q000900213Q00122Q000A000C6Q0007000A00024Q0006000600074Q0005000200024Q000600043Q00202Q0006000600222Q004601076Q00FC00040007000200069A010400B700013Q00040F012Q00B700012Q0046010400013Q0012A9000500233Q00202Q0006000200184Q0005000500064Q0004000200014Q000400086Q0004000100024Q000400043Q00122Q000500043Q00202Q0005000500054Q0005000100022Q004601066Q006501060001000200069A010600B300013Q00040F012Q00B300010020E30006000200240020E300060006002500069A010600B300013Q00040F012Q00B30001001288010600043Q0020E30006000600052Q00650106000100022Q0032010600060005002695000600B30001002600040F012Q00B300012Q004D000600094Q006501060001000200069A010600A800013Q00040F012Q00A800010020E300070002001E0020E300070007002500069A010700A800013Q00040F012Q00A800012Q004D000700073Q0020E300080002001E0020E300080008001C2Q004D000900043Q0020E30009000900222Q0046010A6Q00EE0007000A00012Q004D0007000A3Q0020E300080002001E2Q00330007000200012Q004D000700084Q00650107000100022Q00D0000700073Q000676010400AE0001000700040F012Q00AE000100040F012Q00B30001001288010700133Q0020E3000700070014001216000800274Q003300070002000100040F012Q00880001001288010600133Q0020E3000600060014001216000700154Q00330006000200012Q004601046Q006501040001000200069A010400C700013Q00040F012Q00C700010020E30004000200240020E300040004002500069A010400C700013Q00040F012Q00C700012Q004D00045Q00201200040004002800202Q00050002002400122Q000600043Q00202Q0006000600054Q00060001000200202Q0006000600294Q0004000500062Q004D000400043Q0020E300040004000800069A010400CE00013Q00040F012Q00CE00012Q004D000400054Q0046010500014Q00330004000200012Q000B012Q00017Q000B3Q0003053Q007063612Q6C03053Q00706169727303063Q00737472696E6703053Q006C6F7765722Q0103043Q0066696E6403083Q0064697361626C6564026Q00F03F03093Q00636F2Q6C656374656403063Q006F70656E656403053Q0074616B656E013D3Q0012882Q0100013Q0006B700023Q000100012Q0046017Q00B200010002000200069A2Q01003A00013Q00040F012Q003A000100069A0102003A00013Q00040F012Q003A0001001288010300024Q0046010400024Q00B200030002000500040F012Q00380001001288010800033Q0020E30008000800042Q0046010900064Q009C010800020002002681010700380001000500040F012Q00380001001288010900033Q00207C0009000900064Q000A00083Q00122Q000B00073Q00122Q000C00086Q000D00016Q0009000D000200062Q000900360001000100040F012Q00360001001288010900033Q00207C0009000900064Q000A00083Q00122Q000B00093Q00122Q000C00086Q000D00016Q0009000D000200062Q000900360001000100040F012Q00360001001288010900033Q00207C0009000900064Q000A00083Q00122Q000B000A3Q00122Q000C00086Q000D00016Q0009000D000200062Q000900360001000100040F012Q00360001001288010900033Q0020A60009000900064Q000A00083Q00122Q000B000B3Q00122Q000C00086Q000D00016Q0009000D000200062Q0009003800013Q00040F012Q003800012Q00E7000900014Q00DA000900023Q00062B0003000C0001000200040F012Q000C00012Q00E700036Q00DA000300024Q000B012Q00013Q00013Q00013Q00030D3Q00476574412Q747269627574657300054Q004D7Q00208D5Q00012Q0051012Q00014Q0091017Q000B012Q00017Q000A3Q0003053Q007063612Q6C03093Q00776F726B7370616365030E3Q0046696E6446697273744368696C64030B3Q0043686573744D6F64656C7303063Q00697061697273030B3Q004765744368696C6472656E2Q033Q0049734103053Q004D6F64656C03083Q00426173655061727403043Q004E616D6500394Q0013017Q00132Q015Q0006B700023Q000100052Q0046012Q00014Q004D8Q004D3Q00014Q004D3Q00024Q0046016Q001288010300013Q0006B700040001000100022Q004D3Q00034Q0046012Q00024Q0033000300020001001289000300023Q00202Q00030003000300122Q000500046Q00030005000200062Q0003002700013Q00040F012Q00270001001288010400053Q00208D0005000300062Q00DE000500064Q003501043Q000600040F012Q0025000100208D000900080007001216000B00084Q00FC0009000B0002000657010900220001000100040F012Q0022000100208D000900080007001216000B00094Q00FC0009000B000200069A0109002500013Q00040F012Q002500012Q0046010900024Q0046010A00084Q003300090002000100062B000400180001000200040F012Q00180001001288010400053Q001288010500023Q00208D0005000500062Q00DE000500064Q003501043Q000600040F012Q003500012Q004D000900023Q0020E3000A0008000A2Q007300090009000A00069A0109003500013Q00040F012Q003500012Q0046010900024Q0046010A00084Q003300090002000100062B0004002D0001000200040F012Q002D00012Q00DA3Q00024Q000B012Q00013Q00023Q000F3Q0003063Q00506172656E742Q033Q0049734103053Q004D6F64656C03083Q004261736550617274030E3Q00497344657363656E64616E744F6603093Q00776F726B737061636503183Q0046696E644669727374416E636573746F724F66436C612Q7303043Q004E616D652Q0103053Q007461626C6503063Q00696E736572742Q033Q006F626A03043Q007061727403043Q006E616D652Q033Q0042617501633Q00069A012Q000900013Q00040F012Q000900012Q004D00016Q0073000100013Q0006572Q0100090001000100040F012Q000900010020E300013Q00010006572Q01000A0001000100040F012Q000A00012Q000B012Q00013Q00208D00013Q0002001216000300034Q00FC0001000300020006572Q0100150001000100040F012Q0015000100208D00013Q0002001216000300044Q00FC0001000300020006572Q0100150001000100040F012Q001500012Q000B012Q00014Q004D000100014Q004601026Q009C2Q010002000200069A2Q01002400013Q00040F012Q0024000100208D000200010002001216000400044Q00FC00020004000200069A0102002400013Q00040F012Q0024000100208D000200010005001288010400064Q00FC000200040002000657010200250001000100040F012Q002500012Q000B012Q00014Q004D000200024Q004601036Q009C0102000200020006570102002F0001000100040F012Q002F00012Q004D000200024Q0046010300014Q009C01020002000200069A0102003000013Q00040F012Q003000012Q000B012Q00013Q00208D00023Q0002001216000400044Q00FC00020004000200069A0102003A00013Q00040F012Q003A000100208D00023Q0007001216000400034Q00FC0002000400020006570102003B0001000100040F012Q003B00012Q004601025Q00069A0102004D00013Q00040F012Q004D000100208D000300020002001216000500034Q00FC00030005000200069A0103004D00013Q00040F012Q004D00010020E30003000200082Q004D000400034Q007300040004000300069A0104004D00013Q00040F012Q004D00012Q0046012Q00024Q004D000400014Q0046010500024Q009C01040002000200068E0001004D0001000400040F012Q004D00012Q004D00036Q0073000300033Q00069A0103005200013Q00040F012Q005200012Q000B012Q00014Q004D00035Q00207101033Q000900122Q0003000A3Q00202Q00030003000B4Q000400046Q00053Q000300102Q0005000C3Q00102Q0005000D00014Q000600033Q00202Q00073Q00084Q00060006000700062Q000600600001000100040F012Q006000010012160006000F3Q00105D0105000E00062Q00EE0003000500012Q000B012Q00017Q00033Q0003063Q0069706169727303093Q0047657454612Q676564030C3Q005F436865737454612Q676564000D3Q001288012Q00014Q004D00015Q00208D000100010002001216000300034Q00A12Q0100034Q0035014Q000200040F012Q000A00012Q004D000500014Q0046010600044Q003300050002000100062B3Q00070001000200040F012Q000700012Q000B012Q00017Q000A3Q0003113Q0066697265746F756368696E7465726573742Q033Q0049734103053Q004D6F64656C03063Q00697061697273030E3Q0047657444657363656E64616E747303083Q00426173655061727403053Q007461626C6503063Q00696E73657274026Q00184003053Q007063612Q6C02344Q004D00026Q006501020001000200069A0102000700013Q00040F012Q00070001001288010300013Q000657010300080001000100040F012Q000800012Q000B012Q00014Q0013010300014Q0046010400014Q002301030001000100208D00043Q0002001216000600034Q00FC00040006000200069A0104002700013Q00040F012Q00270001001288010400043Q00208D00053Q00052Q00DE000500064Q003501043Q000600040F012Q0025000100208D000900080002001216000B00064Q00FC0009000B000200069A0109002500013Q00040F012Q002500010006AD000800250001000100040F012Q00250001001288010900073Q0020350009000900084Q000A00036Q000B00086Q0009000B00014Q000900033Q000E2Q000900250001000900040F012Q0025000100040F012Q0027000100062B000400150001000200040F012Q00150001001288010400044Q0046010500034Q00B200040002000600040F012Q003100010012880109000A3Q0006B7000A3Q000100022Q0046012Q00024Q0046012Q00084Q00330009000200012Q000F00075Q00062B0004002B0001000200040F012Q002B00012Q000B012Q00013Q00013Q00063Q0003113Q0066697265746F756368696E746572657374028Q0003043Q007461736B03043Q0077616974027B14AE47E17A943F026Q00F03F000F3Q001288012Q00014Q004D00016Q004D000200013Q001216000300024Q00EE3Q00030001001288012Q00033Q0020E35Q0004001216000100054Q00333Q00020001001288012Q00014Q004D00016Q004D000200013Q001216000300064Q00EE3Q000300012Q000B012Q00017Q00023Q0003053Q007063612Q6C03083Q00746F6E756D626572000E3Q001288012Q00013Q0006B700013Q000100012Q004D8Q00B23Q0002000100069A012Q000B00013Q00040F012Q000B0001001288010200024Q0046010300014Q009C0102000200020006570102000C0001000100040F012Q000C00012Q0062000200024Q00DA000200024Q000B012Q00013Q00013Q00033Q0003043Q004461746103043Q0042656C6903053Q0056616C756500064Q00CA7Q00206Q000100206Q000200206Q00036Q00028Q00017Q000B3Q0003063Q00697061697273030B3Q004765744368696C6472656E03043Q004E616D6503063Q00737472696E6703053Q006D61746368030A3Q005E49736C616E6420256403053Q007063612Q6C03053Q007461626C6503063Q00696E7365727403043Q006E616D652Q033Q00706F73002A4Q0013017Q004D00016Q00652Q01000100020006572Q0100060001000100040F012Q000600012Q00DA3Q00023Q001288010200013Q00208D0003000100022Q00DE000300044Q003501023Q000400040F012Q002600012Q004D000700013Q0020E30008000600032Q009C010700020002000657010700250001000100040F012Q00250001001288010700043Q0020E30007000700050020E3000800060003001216000900064Q00FC000700090002000657010700250001000100040F012Q00250001001288010700073Q0006B700083Q000100012Q0046012Q00064Q00B200070002000800069A0107002500013Q00040F012Q00250001001288010900083Q0020E30009000900092Q0046010A6Q0013010B3Q00020020E3000C0006000300105D010B000A000C00105D010B000B00082Q00EE0009000B00012Q000F00055Q00062B0002000B0001000200040F012Q000B00012Q00DA3Q00024Q000B012Q00013Q00013Q00023Q0003083Q004765745069766F7403083Q00506F736974696F6E00064Q00CD7Q00206Q00016Q0002000200206Q00026Q00028Q00017Q000F3Q00030D3Q0052617963617374506172616D732Q033Q006E6577030A3Q0046696C7465725479706503043Q00456E756D03113Q005261796361737446696C7465725479706503073Q004578636C756465031A3Q0046696C74657244657363656E64616E7473496E7374616E63657303093Q00436861726163746572030B3Q0049676E6F726557617465722Q0103053Q007063612Q6C03083Q00496E7374616E636503083Q00506F736974696F6E03013Q0059026Q0059C001243Q0012882Q0100013Q0020E30001000100022Q00652Q0100010002001288010200043Q0020E30002000200050020E300020002000600105D2Q01000300022Q0013010200014Q004D00035Q0020E30003000300082Q002301020001000100105D2Q010007000200309300010009000A2Q0062000200023Q0012880103000B3Q0006B700043Q000100032Q0046012Q00024Q0046017Q0046012Q00014Q009C01030002000200069A0103002100013Q00040F012Q0021000100069A0102002100013Q00040F012Q002100010020E300040002000C00069A0104002100013Q00040F012Q002100010020E300040002000D0020E300040004000E000ED3000F00210001000400040F012Q002100010020E300040002000D2Q00DA000400024Q0062000400044Q00DA000400024Q000B012Q00013Q00013Q00073Q0003093Q00776F726B737061636503073Q005261796361737403073Q00566563746F72332Q033Q006E6577028Q00025Q0088A340025Q0088B3C000143Q0012E93Q00013Q00206Q00024Q000200013Q00122Q000300033Q00202Q00030003000400122Q000400053Q00122Q000500063Q00122Q000600056Q0003000600024Q00020002000300122Q000300033Q00202Q00030003000400122Q000400053Q00122Q000500073Q00122Q000600056Q0003000600024Q000400028Q000400029Q006Q00017Q000B3Q0003043Q006D6174682Q033Q006D617803083Q00506F736974696F6E03013Q0059025Q00806B4003073Q00566563746F72332Q033Q006E657703013Q005803013Q005A03063Q00434672616D65030A3Q00636865737453702Q6564024C4Q004D00026Q0065010200010002000657010200060001000100040F012Q000600012Q00E700036Q00DA000300023Q001288010300013Q0020E30003000300020020E30004000200030020E30004000400040020E300053Q00042Q00FC0003000500020020AC010300030005001288010400063Q0020E30004000400070020E30005000200030020E30005000500082Q0046010600033Q0020E30007000200030020E30007000700092Q00FC0004000700022Q004D000500013Q0012880106000A3Q0020E30006000600072Q0046010700044Q009C0106000200022Q004D000700023Q0020E300070007000B2Q0046010800014Q00FC000500080002000657010500220001000100040F012Q002200012Q00E700056Q00DA000500024Q0046010500014Q0065010500010002000657010500280001000100040F012Q002800012Q00E700056Q00DA000500023Q001288010500063Q00204600050005000700202Q00063Q00084Q000700033Q00202Q00083Q00094Q0005000800024Q000600013Q00122Q0007000A3Q00202Q0007000700074Q000800056Q0007000200024Q000800023Q00202Q00080008000B4Q000900016Q00060009000200062Q0006003B0001000100040F012Q003B00012Q00E700066Q00DA000600024Q0046010600014Q0065010600010002000657010600410001000100040F012Q004100012Q00E700066Q00DA000600024Q004D000600013Q0012880107000A3Q0020E30007000700072Q004601086Q009C0107000200022Q004D000800023Q0020E300080008000B2Q0046010900014Q0051010600094Q009101066Q000B012Q00017Q00033Q0003053Q00636865737403043Q00646F6E6503073Q007669736974656401093Q002681012Q00080001000100040F012Q000800012Q004D00016Q004D00026Q001301036Q001301045Q00105D01020003000400105D2Q01000200032Q000B012Q00017Q00073Q0003083Q00506F736974696F6E03043Q006D61746803053Q00666C2Q6F7203013Q0058026Q00244003013Q002C03013Q005A010F3Q0020282Q013Q000100122Q000200023Q00202Q00020002000300202Q00030001000400202Q0003000300054Q00020002000200122Q000300063Q00122Q000400023Q00202Q00040004000300202Q00050001000700202Q0005000500054Q0004000200024Q0002000200044Q000200028Q00017Q002D3Q0003153Q00616775617264616E646F20706572736F6E6167656D03043Q007461736B03043Q0077616974026Q00F03F028Q0003063Q0069706169727303043Q00646F6E652Q033Q006F626A03043Q007061727403023Q006F7303053Q00636C6F636B03083Q00506F736974696F6E03093Q004D61676E697475646503093Q00696E646F206174652003043Q006E616D6503023Q00202803043Q006D61746803053Q00666C2Q6F7203023Q006D2903073Q00566563746F72332Q033Q006E6577026Q000840026Q00204003063Q00506172656E7403063Q00434672616D65030A3Q00636865737453702Q6564026Q00D03F00026Q66D63F026Q005E4003223Q0062617520636F6C657461646F3B2070726F637572616E646F206F2070726F78696D6F032C3Q006E616F20636F6E6669726D6569206120636F6C6574613B20766F752074656E746172206E6F76616D656E746503073Q00766973697465642Q033Q00706F73025Q00806640032E3Q00766F6C746120636F6E636C756964613B207265696E696369616E646F206120627573636120706F7220696C686173027Q004003063Q00706F6E746F2003233Q002073656D2074652Q72656E6F3B2070726F637572616E646F206F7574726120696C6861026Q00E03F026Q003240030A3Q00696E646F20706172612003103Q0020706F722063696D6120646F206D6172029A5Q99E93F025Q00E085400257013Q004D00026Q00650102000100020006570102000C0001000100040F012Q000C00012Q0046010300013Q00121B010400016Q00030002000100122Q000300023Q00202Q00030003000300122Q000400046Q0003000200016Q00014Q0062000300043Q0012B2010500053Q00122Q000600066Q000700016Q000700016Q00063Q000800044Q003800010020AC0105000500042Q004D000B00023Q0020E3000B000B00070020E3000C000A00082Q0073000B000B000C2Q004D000C00023Q0020E3000C000C00072Q004D000D00033Q0020E3000E000A00092Q009C010D000200022Q0073000C000C000D00069A010B002500013Q00040F012Q00250001001288010D000A3Q0020E3000D000D000B2Q0065010D00010002000639010D00380001000B00040F012Q0038000100069A010C002C00013Q00040F012Q002C0001001288010D000A3Q0020E3000D000D000B2Q0065010D00010002000639010D00380001000C00040F012Q003800010020E3000D000A0009002064010D000D000C00202Q000E0002000C4Q000D000D000E00202Q000D000D000D00062Q0004003500013Q00040F012Q00350001000676010D00380001000400040F012Q003800012Q0046010E000A4Q00460104000D4Q00460103000E3Q00062B000600130001000200040F012Q0013000100069A010300D400013Q00040F012Q00D400012Q0046010600013Q0012130007000E3Q00202Q00080003000F00122Q000900103Q00122Q000A00113Q00202Q000A000A00124Q000B00046Q000A0002000200122Q000B00136Q00070007000B4Q0006000200012Q004D000600043Q0020E30007000300090020E300070007000C001288010800143Q0020E3000800080015001216000900053Q001216000A00163Q001216000B00054Q00FC0008000B00022Q00330107000700082Q004601086Q00FC00060008000200069A010600D300013Q00040F012Q00D300012Q004D000600054Q0065010600010002001216000700043Q001216000800173Q001216000900043Q0004630007009C00012Q0046010B6Q0065010B0001000200069A010B009C00013Q00040F012Q009C00010020E3000B000300080020E3000B000B001800069A010B009C00013Q00040F012Q009C00010020E3000B000300090020E3000B000B0018000657010B00680001000100040F012Q0068000100040F012Q009C00012Q004D000B6Q0065010B0001000200069A010B008500013Q00040F012Q008500010020E3000C000300090020E3000C000C001800069A010C008500013Q00040F012Q008500012Q004D000C00063Q001248000D00193Q00202Q000D000D001500202Q000E0003000900202Q000E000E000C00122Q000F00143Q00202Q000F000F001500122Q001000053Q00122Q001100043Q00122Q001200056Q000F001200024Q000E000E000F4Q000D000200024Q000E00073Q00202Q000E000E001A4Q000F8Q000C000F00014Q000C00083Q00202Q000D0003000800202Q000E000300094Q000C000E0001001288010C00023Q0020E3000C000C0003001216000D001B4Q0033000C000200012Q004D000C00054Q0065010C000100020020E3000D000300080020E3000D000D001800069A010D009C00013Q00040F012Q009C00012Q004D000D00093Q0020E3000E000300082Q009C010D00020002000657010D009C0001000100040F012Q009C000100267B0006009B0001001C00040F012Q009B000100267B000C009B0001001C00040F012Q009B00010006760106009B0001000C00040F012Q009B000100040F012Q009C00010004060107005B0001001288010700023Q0020E30007000700030012160008001D4Q00330007000200012Q004D000700054Q00650107000100020020E30008000300080020E300080008001800069A010800B200013Q00040F012Q00B200012Q004D000800093Q0020E30009000300082Q009C010800020002000657010800B30001000100040F012Q00B3000100267B000600B10001001C00040F012Q00B1000100267B000700B10001001C00040F012Q00B10001000639010600B20001000700040F012Q00B200012Q001101086Q00E7000800013Q00069A010800B800013Q00040F012Q00B800010012160009001E3Q000657010900B90001000100040F012Q00B90001001216000900174Q004D000A00023Q00206C010A000A000700202Q000B0003000800122Q000C000A3Q00202Q000C000C000B4Q000C000100024Q000C000C00094Q000A000B000C4Q000A00023Q00202Q000A000A00074Q000B00033Q00202Q000C000300094Q000B0002000200122Q000C000A3Q00202Q000C000C000B4Q000C000100024Q000C000C00094Q000A000B000C4Q000A00013Q00062Q000800D100013Q00040F012Q00D10001001216000B001F3Q000657010B00D20001000100040F012Q00D20001001216000B00204Q0033000A000200012Q000B012Q00014Q004D0006000A4Q00650106000100022Q0062000700083Q001288010900064Q0046010A00064Q00B200090002000B00040F012Q00F300012Q004D000E00023Q0020E3000E000E00210020E3000F000D000F2Q0073000E000E000F00069A010E00E600013Q00040F012Q00E60001001288010F000A3Q0020E3000F000F000B2Q0065010F00010002000639010F00F30001000E00040F012Q00F300010020E3000F000D00220020E300100002000C2Q0032010F000F00100020E3000F000F000D000ED3002300F30001000F00040F012Q00F3000100069A010800F000013Q00040F012Q00F00001000676010F00F30001000800040F012Q00F300012Q00460110000D4Q00460108000F4Q0046010700103Q00062B000900DB0001000200040F012Q00DB0001000657010700022Q01000100040F012Q00022Q012Q0046010900013Q001216000A00244Q00330009000200012Q004D000900024Q0013010A5Q00105D01090021000A001288010900023Q0020E3000900090003001216000A00254Q00330009000200012Q000B012Q00014Q004D0009000B3Q0020E3000A000700222Q009C0109000200020006570109001A2Q01000100040F012Q001A2Q012Q004D000A00023Q002012000A000A002100202Q000B0007000F00122Q000C000A3Q00202Q000C000C000B4Q000C0001000200202Q000C000C00234Q000A000B000C2Q0046010A00013Q001262010B00263Q00202Q000C0007000F00122Q000D00276Q000B000B000D4Q000A0002000100122Q000A00023Q00202Q000A000A000300122Q000B00286Q000A000200016Q00013Q001288010A00143Q0020E3000A000A0015001216000B00053Q001216000C00293Q001216000D00054Q00FC000A000D00022Q0033010A0009000A2Q0046010B00013Q001216000C002A3Q0020E3000D0007000F001216000E002B4Q0087000C000C000E2Q0040000B000200014Q000B00046Q000C000A6Q000D8Q000B000D000200062Q000B002E2Q01000100040F012Q002E2Q012Q000B012Q00014Q0046010B6Q0065010B00010002000657010B00332Q01000100040F012Q00332Q012Q000B012Q00013Q001288010B00023Q00200D000B000B000300122Q000C002C6Q000B000200014Q000B8Q000B000100024Q000C5Q00062Q000B004C2Q013Q00040F012Q004C2Q01001288010D00064Q004D000E00014Q0077010E00014Q0035010D3Q000F00040F012Q004A2Q010020E30012001100090020E300120012000C0020E30013000B000C2Q00320112001200130020E300120012000D0026AB0012004A2Q01002D00040F012Q004A2Q012Q00E7000C00013Q00040F012Q004C2Q0100062B000D00412Q01000200040F012Q00412Q01000657010C00562Q01000100040F012Q00562Q012Q004D000D00023Q002012000D000D002100202Q000E0007000F00122Q000F000A3Q00202Q000F000F000B4Q000F0001000200202Q000F000F00234Q000D000E000F2Q000B012Q00017Q00033Q0003073Q0062617274696C6F03043Q0073746570026Q00F03F01053Q002681012Q00040001000100040F012Q000400012Q004D00015Q0030930001000200032Q000B012Q00017Q00243Q00027Q004003253Q006120717565737420646F2042617274696C6F20736F20657869737465206E6F20536561203203043Q007461736B03043Q0077616974025Q00908A4003233Q007072656369736120646F206C6576656C203835302028766F63652065737461206E6F2003013Q002903143Q0042617274696C6F517565737450726F6772652Q7303073Q0042617274696C6F03043Q007374657003043Q007479706503063Q006E756D626572028Q00026Q000840026Q00F03F03423Q0066616C7461206120706172746520646F20436F6C697365752028736F6C746172206F7320676C61646961646F726573293A2066616361206D616E75616C6D656E746503073Q0062617274696C6F030B3Q005377616E2050697261746503063Q004A6572656D7903063Q006A6572656D7903043Q006E616D65030C3Q0042617274696C6F51756573742Q033Q006964782Q033Q006D6F622Q033Q006C6F63030D3Q006B696E67646F6D6F66726F736503043Q00726F7365031F3Q00616775617264616E646F206F204A6572656D792061706172656365723Q2E026Q00F83F03093Q006F2042617274696C6F031D3Q0066616C616E646F20636F6D206F2042617274696C6F2028706172746520030A3Q005374617274517565737403183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C03043Q006D6174682Q033Q006D696E02A44Q004D00026Q00610102000100012Q004D000200013Q00267B0002000D0001000100040F012Q000D00012Q0046010200013Q00121B010300026Q00020002000100122Q000200033Q00202Q00020002000400122Q000300016Q0002000200016Q00014Q004D000200024Q00650102000100020026950002001D0001000500040F012Q001D00012Q0046010200013Q001206000300066Q000400026Q00040001000200122Q000500076Q0003000300054Q00020002000100122Q000200033Q00202Q00020002000400122Q000300016Q0002000200016Q00014Q004D000200033Q0012A2010300083Q00122Q000400096Q0002000400024Q000300043Q00202Q00030003000A00122Q0004000B6Q000500026Q00040002000200262Q0004002D0001000C00040F012Q002D0001000EF3000D002D0001000200040F012Q002D00010026AB0002002D0001000E00040F012Q002D00010020AC01030002000F000EF3000E00370001000300040F012Q003700012Q0046010400013Q001286010500106Q0004000200014Q000400053Q00122Q000500116Q00068Q0004000600016Q00013Q0026810103003C0001000F00040F012Q003C0001001216000400123Q0006570104003D0001000100040F012Q003D0001001216000400133Q0026810103004A0001000100040F012Q004A00012Q004D000500064Q0013010600013Q001216000700144Q0023010600010001001216000700134Q004601086Q0046010900014Q00FC00050009000200069A0105004A00013Q00040F012Q004A00012Q000B012Q00014Q004D000500074Q0046010600044Q009C01050002000200069A0105006B00013Q00040F012Q006B0001002681010300630001000F00040F012Q006300012Q004D000500084Q00B500063Q000300302Q00060015001600302Q00060017000F00302Q0006001800124Q00078Q00083Q00014Q000900023Q00122Q000A001A3Q00122Q000B001B6Q00090002000100105D0108001900092Q005F010900026Q0009000100024Q000A8Q000B00016Q0005000B000100044Q006A00012Q0046010500013Q0012160006001C4Q0033000500020001001288010500033Q0020E30005000500040012160006001D4Q00330005000200012Q000B012Q00014Q004D000500094Q0013010600013Q001216000700114Q00230106000100012Q0013010700023Q0012160008001A3Q0012160009001B4Q00230107000200012Q004601086Q0046010900013Q001216000A001E4Q00FC0005000A000200069A0105007D00013Q00040F012Q007D00012Q004601066Q00650106000100020006570106007E0001000100040F012Q007E00012Q000B012Q00014Q0046010600013Q0012B00107001F6Q000800033Q00122Q000900076Q0007000700094Q0006000200014Q000600033Q00122Q000700203Q00122Q000800166Q000900036Q0006000900012Q004D0006000A3Q00208D000700050021001216000900224Q00A1010700094Q00F700063Q0001001288010600033Q0020E3000600060004001216000700014Q00330006000200012Q004D000600074Q0046010700044Q009C010600020002000657010600A30001000100040F012Q00A300010012880106000B4Q0046010700024Q009C01060002000200267B000600A30001000C00040F012Q00A300012Q004D000600043Q00121D000700233Q00202Q00070007002400202Q00080003000F00122Q0009000E6Q00070009000200102Q0006000A00072Q000B012Q00017Q00193Q00026Q00084003223Q006120436974697A656E20517565737420736F20657869737465206E6F20536561203303043Q007461736B03043Q0077616974027Q0040025Q00209C4003153Q007072656369736120646F206C6576656C2031382Q30030F3Q006361707461696E656C657068616E7403103Q004361707461696E20456C657068616E7403073Q00636974697A656E030E3Q00666C6F6174696E67747572746C6503063Q00747572746C6503093Q006F20436974697A656E031A3Q00706567616E646F206120436974697A656E2051756573743Q2E030A3Q0053746172745175657374030C3Q00436974697A656E5175657374026Q00F03F03183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C026Q00F83F2Q033Q007965732Q033Q0073696D03063Q00612Q6365707403073Q0061636569746172032C3Q00717565737420706567612E20416775617264616E646F206F204361707461696E20456C657068616E743Q2E025D4Q004D00026Q00610102000100012Q004D000200013Q00267B0002000D0001000100040F012Q000D00012Q0046010200013Q00121B010300026Q00020002000100122Q000200033Q00202Q00020002000400122Q000300056Q0002000200016Q00014Q004D000200024Q0065010200010002002695000200190001000600040F012Q001900012Q0046010200013Q00121B010300076Q00020002000100122Q000200033Q00202Q00020002000400122Q000300056Q0002000200016Q00014Q004D000200034Q0013010300013Q001216000400084Q0023010300010001001216000400094Q004601056Q0046010600014Q00FC00020006000200069A0102002400013Q00040F012Q002400012Q000B012Q00014Q004D000200044Q0013010300013Q0012160004000A4Q00230103000100012Q0013010400023Q0012160005000B3Q0012160006000C4Q00230104000200012Q004601056Q0046010600013Q0012160007000D4Q00FC00020007000200069A0102003600013Q00040F012Q003600012Q004601036Q0065010300010002000657010300370001000100040F012Q003700012Q000B012Q00014Q0046010300013Q0012160004000E4Q00330003000200012Q004D000300053Q0012160004000F3Q001216000500103Q001216000600114Q00EE0003000600012Q004D000300063Q00208D000400020012001216000600134Q00A1010400064Q00FA00033Q000100122Q000300033Q00202Q00030003000400122Q000400146Q0003000200014Q000300076Q000400043Q00122Q000500153Q00122Q000600163Q00122Q000700173Q001216000800184Q00230104000400012Q00E7000500014Q009C00030005000100122Q000300033Q00202Q00030003000400122Q000400056Q0003000200014Q000300013Q00122Q000400196Q00030002000100122Q000300033Q00202Q00030003000400122Q000400016Q0003000200016Q00017Q00073Q0003053Q00736162657203073Q006C617374476574028Q0003043Q0073746570034Q0003053Q007374616765026Q00F03F01083Q002681012Q00070001000100040F012Q000700012Q00132Q013Q00030030930001000200030030930001000400050030930001000600072Q00B800016Q000B012Q00017Q00993Q00026Q00F03F03203Q006120517565737420536162657220736F20657869737465206E6F20536561203103043Q007461736B03043Q0077616974027Q0040026Q00694003233Q007072656369736120646F206C6576656C20322Q302028766F63652065737461206E6F2003013Q002903253Q00566F6365206A612074656D206F2053616265722E20517565737420636F6E636C756964612E026Q00084003093Q00776F726B7370616365030E3Q0046696E6446697273744368696C642Q033Q004D617003063Q004A756E676C6503063Q00446573657274030B3Q005175657374506C6174657303043Q00442Q6F722Q033Q0049734103083Q004261736550617274030C3Q005472616E73706172656E6379028Q00030B3Q007361626572506C61746573030B3Q00706C61746550612Q7365732Q01032F3Q00536162657220312F353A20706973616E646F206E617320706C616361732064612053656C76612028726F64616461202Q033Q002F3229026Q00244003053Q00506C617465026Q00D03F03043Q004275726E03043Q005061727403163Q0046696E6446697273744368696C64576869636849734103093Q0073616265724275726E033D3Q00536162657220322F353A20717565696D616E646F20612062612Q726569726120646F204465736572746F20287072656369736120646120546F7263682903053Q00546F72636803063Q00697061697273030E3Q0047657444657363656E64616E747303063Q00737472696E6703053Q006C6F77657203043Q004E616D6503053Q00746F726368030E3Q00497344657363656E64616E744F6603093Q0043686172616374657203043Q00542Q6F6C03053Q004D6F64656C03083Q00506F736974696F6E03093Q004D61676E6974756465032E3Q00536162657220322F353A20616368656920756D6120546F726368206E6F206D6170612C20696E646F20706567617203063Q00434672616D652Q033Q006E657703073Q00566563746F7233030A3Q0074772Q656E53702Q6564026Q33D33F03063Q0048616E646C65030F3Q0050726F78696D69747950726F6D707403053Q007063612Q6C030D3Q00436C69636B4465746563746F7203083Q004261636B7061636B030B3Q004765744368696C6472656E03383Q00536162657220322F353A206E616F206163686569206E656E68756D6120546F726368206E6F206D6170612E2053657573206974656E733A2003053Q007461626C6503063Q00636F6E63617403023Q002C2003073Q0052617963617374025Q00C082C0026Q001040026Q00184003043Q006D6174682Q033Q006D617803053Q007374616765030A3Q007361626572537461676503193Q00536162657220332F353A20706567616E646F206F20636F706F03103Q0050726F517565737450726F6772652Q7303063Q0047657443757003083Q0063757054726965732Q033Q0043757003043Q0066696E6403043Q006472697003073Q0064726F706C657403093Q00776174657264726F7003043Q00676F746103043Q006C65616B03063Q0066726F7A656E03043Q00736E6F772Q033Q0069636503593Q00536162657220332F353A206E616F20616368656920612056696C6120436F6E67656C616461206E656D206120676F74612E20566120617465206120676F74612065206D652064696761206F206E6F6D6520646F206C6F63616C03353Q00536162657220332F353A206C6576616E646F206F20636F706F20617465206120676F7461202856696C6120436F6E67656C61646129026Q00344003093Q0066692Q6C537461727403023Q006F7303053Q00636C6F636B03073Q0046692Q6C43757003063Q00506172656E74026Q0044400003043Q004E50437303083Q005369636B204D616E026Q00284003203Q00536162657220332F353A20696E646F20617465206F205369636B204D616E202803053Q00666C2Q6F7203023Q006D2903213Q00536162657220332F353A2066616C616E646F20636F6D206F205369636B204D616E03073Q005369636B4D616E029A5Q99E93F2Q033Q007965732Q033Q0073696D03063Q00612Q6365707403073Q006163656974617203023Q006F6B03083Q00636F6E74696E756503093Q007369636B547269657303253Q00536162657220332F353A206E616F20616368656920612056696C6120436F6E67656C616461025Q00C06240032F3Q00536162657220332F353A20696E646F207061726120612056696C6120436F6E67656C61646120286D656E6469676F2903073Q00456E656D69657303153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F696403163Q00476574506C6179657246726F6D436861726163746572026Q007940025Q00C0724003043Q007369636B03063Q0062652Q67617203073Q006D656E6469676F03083Q00686F6D656C652Q7303043Q00702Q6F722Q033Q006F6C6403013Q006D03013Q00702Q033Q0070726903043Q00736F727403343Q00536162657220332F353A206E656E68756D204E50432061636861646F20706572746F2064612056696C6120436F6E67656C616461026Q00F83F03063Q006E706349647803173Q00536162657220332F353A2066616C616E646F20636F6D2003023Q00202803013Q002F030A3Q0029207C204E5043733A2003053Q006C6F674174031A3Q005B4F72696F6E2053616265725D204E50437320706572746F3A2003093Q006D6F626C6561646572030A3Q004D6F62204C656164657203093Q007361774C6561646572031D3Q00536162657220342F353A20656E74726567616E646F206F2052656C696303073Q0052696368536F6E030A3Q00506C61636552656C6963030A3Q0072656C69635472696573030B3Q00736162657265787065727403063Q006A756E676C65030C3Q005F576F726C644F726967696E030B3Q00456E656D79537061776E7303373Q00536162657220352F353A20696E646F207061726120612053656C76612070617261206F20536162657220457870657274206E617363657203343Q00536162657220352F353A206E612053656C76612C206573706572616E646F206F20536162657220457870657274206E617363657203703Q00536162657220352F353A20657461706173206A61206665697461733B206573706572616E646F206F2053616265722045787065727420746F6D61722064616E6F20287573652027526573657461722070726F6772652Q736F20646F20536162657227207061726120726566617A65722902A6053Q004D00026Q00610102000100012Q004D000200013Q00267B0002000D0001000100040F012Q000D00012Q0046010200013Q00121B010300026Q00020002000100122Q000200033Q00202Q00020002000400122Q000300056Q0002000200016Q00014Q004D000200024Q00650102000100020026950002001D0001000600040F012Q001D00012Q0046010200013Q001206000300076Q000400026Q00040001000200122Q000500086Q0003000300054Q00020002000100122Q000200033Q00202Q00020002000400122Q000300056Q0002000200016Q00013Q0006B700023Q000100032Q004D3Q00034Q004D3Q00044Q004D3Q00053Q0006B700030001000100012Q004D3Q00064Q0046010400034Q006501040001000200069A0104002F00013Q00040F012Q002F00012Q0046010400013Q00121B010500096Q00040002000100122Q000400033Q00202Q00040004000400122Q0005000A6Q0004000200016Q00013Q0006B700040002000100052Q004D3Q00054Q004D3Q00074Q0046017Q004D3Q00084Q0046012Q00013Q0012880105000B3Q00208D00050005000C0012160007000D4Q00FC0005000700020006210006003E0001000500040F012Q003E000100208D00060005000C0012160008000E4Q00FC000600080002000621000700430001000500040F012Q0043000100208D00070005000C0012160009000F4Q00FC0007000900020006B700080003000100052Q004D3Q00094Q004D3Q000A4Q0046017Q004D3Q000B4Q004D3Q00033Q000285000900043Q0006B7000A0005000100012Q004D3Q00063Q00069A0106005900013Q00040F012Q0059000100208D000B0006000C001216000D00104Q00FC000B000D0002000657010B005F0001000100040F012Q005F000100208D000B0006000C001216000D00104Q00E7000E00014Q00FC000B000E0002000657010B005F0001000100040F012Q005F0001000621000B005F0001000500040F012Q005F000100208D000B0005000C001216000D00104Q00E7000E00014Q00FC000B000E0002000621000C006A0001000B00040F012Q006A000100208D000C000B000C001216000E00114Q00FC000C000E0002000657010C006A0001000100040F012Q006A000100208D000C000B000C001216000E00114Q00E7000F00014Q00FC000C000F000200069A010C00BE00013Q00040F012Q00BE000100208D000D000C0012001216000F00134Q00FC000D000F000200069A010D00BE00013Q00040F012Q00BE00010020E3000D000C0014002681010D00BE0001001500040F012Q00BE00012Q004D000D00033Q0020E3000D000D0016000657010D00BE0001000100040F012Q00BE00012Q004D000D00053Q0020E3000D000D0017000657010D007D0001000100040F012Q007D0001001216000D00153Q002695000D00BE0001000500040F012Q00BE00012Q004D000D00054Q004D000E00053Q0020E3000E000E0017000657010E00850001000100040F012Q00850001001216000E00153Q0020AC010E000E000100105D010D0017000E2Q004D000D00053Q0020E3000D000D0017000EF30005008F0001000D00040F012Q008F00012Q004D000D00033Q003093000D001600182Q004D000D00044Q0061010D000100012Q0046010D00013Q001216000E00194Q004D000F00053Q0020E3000F000F00170012160010001A4Q0087000E000E00102Q0033000D00020001001216000D00013Q001216000E001B3Q001216000F00013Q000463000D00B900012Q004601116Q00650111000100020006570111009F0001000100040F012Q009F00012Q000B012Q00013Q00208D0011000B000C0012160013001C4Q0046011400104Q00870013001300142Q00FC0011001300022Q0046011200094Q0046011300114Q009C01120002000200069A011200B800013Q00040F012Q00B800012Q0046011300084Q0046011400124Q003300130002000100208D001300110012001216001500134Q00FC00130015000200069A011300B400013Q00040F012Q00B400012Q004D0013000C4Q0046011400114Q0033001300020001001288011300033Q0020E30013001300040012160014001D4Q0033001300020001000406010D009A0001001288010D00033Q0020E3000D000D0004001216000E00014Q0033000D000200012Q000B012Q00013Q00069A010C00D000013Q00040F012Q00D0000100208D000D000C0012001216000F00134Q00FC000D000F000200069A010D00D000013Q00040F012Q00D000010020E3000D000C001400267B000D00D00001001500040F012Q00D000012Q004D000D00033Q0020E3000D000D0016000657010D00D00001000100040F012Q00D000012Q004D000D00033Q003093000D001600182Q004D000D00044Q0061010D0001000100069A010700DD00013Q00040F012Q00DD000100208D000D0007000C001216000F001E4Q00FC000D000F0002000657010D00E30001000100040F012Q00E3000100208D000D0007000C001216000F001E4Q00E7001000014Q00FC000D00100002000657010D00E30001000100040F012Q00E30001000621000D00E30001000500040F012Q00E3000100208D000D0005000C001216000F001E4Q00E7001000014Q00FC000D00100002000621000E00EE0001000D00040F012Q00EE000100208D000E000D000C0012160010001F4Q00FC000E00100002000657010E00EE0001000100040F012Q00EE000100208D000E000D0020001216001000134Q00E7001100014Q00FC000E0011000200069A010E00FB00013Q00040F012Q00FB00010020E3000F000E001400267B000F00FB0001001500040F012Q00FB00012Q004D000F00033Q0020E3000F000F0021000657010F00FB0001000100040F012Q00FB00012Q004D000F00033Q003093000F002100182Q004D000F00044Q0061010F0001000100069A010E000902013Q00040F012Q000902010020E3000F000E0014002681010F00090201001500040F012Q000902012Q004D000F00033Q0020E3000F000F0021000657010F00090201000100040F012Q000902012Q0046010F00013Q001216001000224Q0033000F000200012Q0046010F000A3Q001216001000234Q009C010F00020002000657010F00DE2Q01000100040F012Q00DE2Q012Q0062001000103Q001288011100243Q0012880112000B3Q00208D0012001200252Q00DE001200134Q003501113Q001300040F012Q00492Q01001288011600263Q0020E30016001600270020E30017001500282Q009C011600020002002681011600492Q01002900040F012Q00492Q0100208D00160015002A2Q004D001800063Q0020E300180018002B0006570118001F2Q01000100040F012Q001F2Q010012880118000B4Q00FC001600180002000657011600492Q01000100040F012Q00492Q0100208D0016001500120012160018002C4Q00FC001600180002000657011600312Q01000100040F012Q00312Q0100208D0016001500120012160018002D4Q00FC001600180002000657011600312Q01000100040F012Q00312Q0100208D001600150012001216001800134Q00FC00160018000200069A011600492Q013Q00040F012Q00492Q012Q0046011600094Q0046011700154Q009C0116000200022Q004D001700094Q006501170001000200069A011600492Q013Q00040F012Q00492Q0100069A011700492Q013Q00040F012Q00492Q010006570110003D2Q01000100040F012Q003D2Q012Q0046011000153Q0020E300180017002E2Q00320118001600180020E300180018002F2Q0046011900094Q0046011A00104Q009C0119000200020020E3001A0017002E2Q003201190019001A0020E300190019002F000676011800492Q01001900040F012Q00492Q012Q0046011000153Q00062B001100132Q01000200040F012Q00132Q0100069A011000A22Q013Q00040F012Q00A22Q012Q0046011100013Q001216001200304Q00330011000200012Q0046011100094Q0046011200104Q009C0111000200022Q0046011200084Q0046011300114Q00330012000200012Q004D0012000B3Q001288011300313Q0020E3001300130032001203001400333Q00202Q00140014003200122Q001500153Q00122Q0016000A3Q00122Q001700156Q0014001700024Q0014001100144Q0013000200024Q001400033Q00202Q0014001400342Q004601156Q00EE001200150001001288011200033Q0020E3001200120004001216001300354Q003300120002000100208D0012001000120012160014002C4Q00FC00120014000200069A011200732Q013Q00040F012Q00732Q0100208D00120010000C001216001400364Q00FC0012001400020006570112007E2Q01000100040F012Q007E2Q0100208D001200100012001216001400134Q00FC00120014000200069A0112007A2Q013Q00040F012Q007A2Q0100068E0012007E2Q01001000040F012Q007E2Q0100208D001200100020001216001400134Q00E7001500014Q00FC00120015000200069A011200832Q013Q00040F012Q00832Q012Q004D0013000C4Q0046011400124Q0033001300020001001288011300243Q00208D0014001000252Q00DE001400154Q003501133Q001500040F012Q009B2Q0100208D001800170012001216001A00374Q00FC0018001A000200069A011800912Q013Q00040F012Q00912Q01001288011800383Q0006B700190006000100012Q0046012Q00174Q003300180002000100208D001800170012001216001A00394Q00FC0018001A000200069A0118009A2Q013Q00040F012Q009A2Q01001288011800383Q0006B700190007000100012Q0046012Q00174Q00330018000200012Q000F00165Q00062B001300882Q01000200040F012Q00882Q01001288011300033Q0020E3001300130004001216001400014Q003300130002000100040F012Q00B92Q012Q001301115Q001280001200246Q001300063Q00202Q00130013003A00202Q00130013003B4Q001300146Q00123Q001400044Q00AE2Q012Q00D0001700113Q0020AC0117001700010020E30018001600282Q009E00110017001800062B001200AA2Q01000200040F012Q00AA2Q012Q0046011200013Q0012160013003C3Q0012880114003D3Q0020E300140014003E2Q0046011500113Q0012160016003F4Q00FC0014001600022Q00870013001300142Q00330012000200012Q004D001100094Q006501110001000200069A011100D92Q013Q00040F012Q00D92Q010012880112000B3Q00208D0012001200400020E300140011002E001288011500333Q0020E3001500150032001216001600153Q001216001700413Q001216001800154Q00A1011500184Q000400123Q000200069A011200D92Q013Q00040F012Q00D92Q012Q004D0013000B3Q001288011400313Q0020E30014001400320020E300150012002E001203001600333Q00202Q00160016003200122Q001700153Q00122Q001800423Q00122Q001900156Q0016001900024Q0015001500164Q0014000200024Q001500033Q00202Q0015001500342Q004601166Q00EE001300160001001288011200033Q0020E3001200120004001216001300054Q00330012000200012Q000B012Q00013Q0020E30010000E002E2Q00FF0011000B3Q00122Q001200313Q00202Q00120012003200122Q001300333Q00202Q00130013003200122Q001400153Q00122Q0015000A3Q00122Q001600436Q0013001600024Q0013001000134Q0012000200024Q001300033Q00202Q0013001300344Q00148Q00110014000100122Q001100033Q00202Q00110011000400122Q001200356Q00110002000100122Q001100243Q00202Q0012000D00254Q001200136Q00113Q001300044Q00FF2Q0100208D001600150012001216001800134Q00FC00160018000200069A011600FF2Q013Q00040F012Q00FF2Q012Q004D0016000C4Q0046011700154Q003300160002000100062B001100F72Q01000200040F012Q00F72Q012Q004D0011000C4Q00460112000E4Q0033001100020001001288011100033Q0020E3001100110004001216001200014Q00330011000200012Q000B012Q00013Q001288010F00443Q0020E3000F000F00452Q004D001000053Q0020E3001000100046000657011000100201000100040F012Q00100201001216001000014Q004D001100033Q0020E3001100110047000657011100150201000100040F012Q00150201001216001100014Q00FC000F001100020006B700100008000100012Q004D3Q00063Q002681010F00FB0201000100040F012Q00FB02012Q0046011100104Q0065011100010002000657011100400201000100040F012Q004002012Q0046011200013Q001216001300484Q00330012000200012Q004D0012000D3Q001216001300493Q0012160014004A4Q00EE001200140001001288011200033Q0020E3001200120004001216001300014Q00330012000200012Q0046011200104Q0065011200010002000657011200350201000100040F012Q003502012Q004D001200054Q004D001300053Q0020E300130013004B000657011300330201000100040F012Q00330201001216001300153Q0020AC01130013000100105D0112004B00132Q004D001200053Q0020E300120012004B0006570112003A0201000100040F012Q003A0201001216001200153Q000EF30042003F0201001200040F012Q003F02012Q0046011200023Q001216001300054Q00330012000200012Q000B012Q00014Q00460112000A3Q0012410113004C6Q0012000200014Q001200123Q00122Q001300243Q00062Q001400480201000500040F012Q004802010012880114000B3Q00208D0014001400252Q00DE001400154Q003501133Q001500040F012Q008E0201001288011800263Q0020E30018001800270020E30019001700282Q009C01180002000200208D001900170012001216001B00134Q00FC0019001B00020006570119005A0201000100040F012Q005A020100208D001900170012001216001B002D4Q00FC0019001B000200069A0119008E02013Q00040F012Q008E0201001288011900263Q00207C00190019004D4Q001A00183Q00122Q001B004E3Q00122Q001C00016Q001D00016Q0019001D000200062Q001900870201000100040F012Q00870201001288011900263Q00207C00190019004D4Q001A00183Q00122Q001B004F3Q00122Q001C00016Q001D00016Q0019001D000200062Q001900870201000100040F012Q00870201001288011900263Q00207C00190019004D4Q001A00183Q00122Q001B00503Q00122Q001C00016Q001D00016Q0019001D000200062Q001900870201000100040F012Q00870201001288011900263Q00207C00190019004D4Q001A00183Q00122Q001B00513Q00122Q001C00016Q001D00016Q0019001D000200062Q001900870201000100040F012Q00870201001288011900263Q0020A600190019004D4Q001A00183Q00122Q001B00523Q00122Q001C00016Q001D00016Q0019001D000200062Q0019008E02013Q00040F012Q008E02012Q0046011900094Q0046011A00174Q009C0119000200022Q0046011200193Q00069A0112008E02013Q00040F012Q008E020100040F012Q0090020100062B0013004C0201000200040F012Q004C0201000657011200A00201000100040F012Q00A002012Q004D0013000E3Q001216001400534Q009C01130002000200068E001200A00201001300040F012Q00A002012Q004D0013000E3Q001216001400544Q009C01130002000200068E001200A00201001300040F012Q00A002012Q004D0013000E3Q001216001400554Q009C0113000200022Q0046011200133Q000657011200AA0201000100040F012Q00AA02012Q0046011300013Q00121B011400566Q00130002000100122Q001300033Q00202Q00130013000400122Q001400056Q0013000200016Q00014Q0046011300013Q001216001400574Q00330013000200012Q004D001300094Q006501130001000200069A011300BA02013Q00040F012Q00BA02010020E300140013002E2Q00320114001400120020E300140014002F000ED3005800BA0201001400040F012Q00BA02012Q0046011400084Q0046011500124Q00330014000200012Q000B012Q00014Q004D001400054Q004D001500053Q0020E3001500150059000657011500C20201000100040F012Q00C202010012880115005A3Q0020E300150015005B2Q006501150001000200105D0114005900152Q004D0014000D3Q001216001500493Q0012160016005C4Q0046011700114Q00EE001400170001001288011400243Q0012880115000B3Q00208D0015001500252Q00DE001500164Q003501143Q001600040F012Q00E7020100208D001900180012001216001B00374Q00FC0019001B000200069A011900E602013Q00040F012Q00E602010020E300190018005D00069A011900E602013Q00040F012Q00E602012Q0046011900093Q0020E3001A0018005D2Q009C01190002000200069A011900E602013Q00040F012Q00E602012Q0046011900093Q002072001A0018005D4Q0019000200024Q00190019001200202Q00190019002F00262Q001900E60201005E00040F012Q00E60201001288011900383Q0006B7001A0009000100012Q0046012Q00184Q00330019000200012Q000F00175Q00062B001400CE0201000200040F012Q00CE0201001288011400033Q0020E3001400140004001216001500014Q00330014000200010012880114005A3Q0020E300140014005B2Q00650114000100022Q004D001500053Q0020E30015001500592Q0032011400140015000ED3004300FA0201001400040F012Q00FA02012Q0046011400023Q001216001500054Q00330014000200012Q004D001400053Q00309300140059005F2Q000B012Q00013Q002681010F00140501000500040F012Q001405012Q004D001100094Q0065011100010002000657011100020301000100040F012Q000203012Q000B012Q00013Q0012880112000B3Q00208D00120012000C001216001400604Q00FC0012001400020006210013000B0301001200040F012Q000B030100208D00130012000C001216001500614Q00FC00130015000200069A0113008803013Q00040F012Q008803012Q0046011400094Q0046011500134Q009C01140002000200069A0114008803013Q00040F012Q008803010020E300150011002E2Q00320115001500140020E300150015002F000ED3006200300301001500040F012Q003003012Q0046011600013Q00129E011700633Q00122Q001800443Q00202Q0018001800644Q001900156Q00180002000200122Q001900656Q0017001700194Q0016000200014Q0016000B3Q00122Q001700313Q0020E3001700170032001203001800333Q00202Q00180018003200122Q001900153Q00122Q001A000A3Q00122Q001B00426Q0018001B00024Q0018001400184Q0017000200024Q001800033Q00202Q0018001800342Q004601196Q00EE0016001900012Q000B012Q00014Q0046011600013Q001216001700664Q00330016000200012Q00460116000A3Q0012160017004C4Q009C0116000200022Q004D0017000F4Q0046011800134Q0033001700020001001288011700243Q00208D0018001300252Q00DE001800194Q003501173Q001900040F012Q0051030100208D001C001B0012001216001E00394Q00FC001C001E000200069A011C004703013Q00040F012Q00470301001288011C00383Q0006B7001D000A000100012Q0046012Q001B4Q0033001C0002000100208D001C001B0012001216001E00374Q00FC001C001E000200069A011C005003013Q00040F012Q00500301001288011C00383Q0006B7001D000B000100012Q0046012Q001B4Q0033001C000200012Q000F001A5Q00062B0017003E0301000200040F012Q003E03012Q004D001700103Q00069A0117005A03013Q00040F012Q005A0301001288011700383Q0006B70018000C000100012Q004D3Q00104Q003300170002000100069A0116006103013Q00040F012Q006103012Q004D0017000D3Q001216001800493Q0012160019005C4Q0046011A00164Q00EE0017001A00012Q004D0017000D3Q001216001800493Q001216001900674Q00EE001700190001001288011700033Q0020E3001700170004001216001800684Q00330017000200012Q004D001700114Q0013011800063Q001216001900693Q001216001A006A3Q00121C001B006B3Q00122Q001C006C3Q00122Q001D006D3Q00122Q001E006E6Q0018000600012Q00E7001900014Q006D01170019000100122Q001700033Q00202Q00170017000400122Q001800016Q0017000200014Q001700056Q001800053Q00202Q00180018006F00062Q0018007E0301000100040F012Q007E0301001216001800153Q0020AC01180018000100105D0117006F00182Q004D001700053Q0020E300170017006F000EF3004200870301001700040F012Q008703012Q0046011700023Q0012160018000A4Q00330017000200012Q000B012Q00014Q004D0014000E3Q001216001500534Q009C011400020002000657011400950301000100040F012Q009503012Q004D0014000E3Q001216001500544Q009C011400020002000657011400950301000100040F012Q009503012Q004D0014000E3Q001216001500554Q009C0114000200022Q004D001500094Q006501150001000200069A0114009B03013Q00040F012Q009B0301000657011500A30301000100040F012Q00A303012Q0046011600013Q00121B011700706Q00160002000100122Q001600033Q00202Q00160016000400122Q001700056Q0016000200016Q00013Q0020E300160015002E2Q00320116001600140020E300160016002F000ED3007100AF0301001600040F012Q00AF03012Q0046011600013Q001225001700726Q0016000200014Q001600086Q001700146Q0016000200016Q00014Q001301165Q0012010017000B3Q00202Q00170017000C00122Q001900736Q00170019000200122Q001800243Q00122Q0019000B3Q00202Q0019001900254Q0019001A6Q00183Q001A00044Q0039040100208D001D001C0012001216001F002D4Q00FC001D001F000200069A011D00CE03013Q00040F012Q00CE030100208D001D001C0074001216001F00754Q00FC001D001F0002000657011D00CE0301000100040F012Q00CE030100208D001D001C0020001216001F00374Q00E7002000014Q00FC001D00200002000657011D00CE0301000100040F012Q00CE030100208D001D001C0020001216001F00394Q00E7002000014Q00FC001D0020000200069A011D003904013Q00040F012Q0039040100069A011700D703013Q00040F012Q00D7030100208D001E001C002A2Q0046012000174Q00FC001E00200002000657011E00390401000100040F012Q003904012Q004D001E00123Q00208D001E001E00762Q00460120001C4Q00FC001E00200002000657011E00390401000100040F012Q0039040100208D001E001C002A2Q004D002000063Q0020E300200020002B000657012000E30301000100040F012Q00E303010012880120000B4Q00FC001E00200002000657011E00390401000100040F012Q003904012Q0046011E00094Q0046011F001C4Q009C011E0002000200069A011E003904013Q00040F012Q003904012Q0032011F001E00140020E3001F001F002F0026F1001F00F40301007700040F012Q00F403010020E3001F0015002E2Q0032011F001E001F0020E3001F001F002F002695001F00390401007800040F012Q00390401001288011F00263Q0020E3001F001F00270020E30020001C00282Q009C011F00020002001288012000263Q00207C00200020004D4Q0021001F3Q00122Q002200793Q00122Q002300016Q002400016Q00200024000200062Q0020002E0401000100040F012Q002E0401001288012000263Q00207C00200020004D4Q0021001F3Q00122Q0022007A3Q00122Q002300016Q002400016Q00200024000200062Q0020002E0401000100040F012Q002E0401001288012000263Q00207C00200020004D4Q0021001F3Q00122Q0022007B3Q00122Q002300016Q002400016Q00200024000200062Q0020002E0401000100040F012Q002E0401001288012000263Q00207C00200020004D4Q0021001F3Q00122Q0022007C3Q00122Q002300016Q002400016Q00200024000200062Q0020002E0401000100040F012Q002E0401001288012000263Q00207C00200020004D4Q0021001F3Q00122Q0022007D3Q00122Q002300016Q002400016Q00200024000200062Q0020002E0401000100040F012Q002E0401001288012000263Q0020A600200020004D4Q0021001F3Q00122Q0022007E3Q00122Q002300016Q002400016Q00200024000200062Q0020003104013Q00040F012Q00310401001216002000153Q000657012000320401000100040F012Q00320401001216002000014Q00D0002100163Q0020AC0121002100012Q001301223Q000300105D0122007F001C00105D01220080001E00105D0122008100202Q009E00160021002200062B001800BA0301000200040F012Q00BA03010012880118003D3Q0020E30018001800822Q0046011900163Q0006B7001A000D000100012Q0046012Q00154Q00C70018001A00014Q00185Q00122Q001900246Q001A00166Q00190002001B00044Q004B04012Q00D0001E00183Q0020AC011E001E00010020E3001F001D007F0020E3001F001F00282Q009E0018001E001F00062B001900460401000200040F012Q004604012Q00D0001900163Q002681011900670401001500040F012Q006704012Q0046011900013Q001216001A00834Q00330019000200012Q004D001900054Q004D001A00053Q0020E3001A001A006F000657011A00590401000100040F012Q00590401001216001A00153Q0020AC011A001A000100105D0119006F001A2Q004D001900053Q0020E300190019006F000EF3004200620401001900040F012Q006204012Q0046011900023Q001216001A000A4Q0033001900020001001288011900033Q0020E3001900190004001216001A00844Q00330019000200012Q000B012Q00014Q004D001900053Q0020E30019001900850006570119006C0401000100040F012Q006C0401001216001900154Q00D0001A00164Q009201190019001A00202Q0019001900014Q001A00053Q00102Q001A008500194Q001A001600194Q001B00013Q00122Q001C00863Q00202Q001D001A007F00202Q001D001D002800122Q001E00874Q0046011F00193Q001216002000884Q00AB012100163Q00122Q002200893Q00122Q0023003D3Q00202Q00230023003E4Q002400183Q00122Q0025003F6Q0023002500024Q001C001C00232Q0074001B000200014Q001B000B3Q00122Q001C00313Q00202Q001C001C003200202Q001D001A008000122Q001E00333Q00202Q001E001E003200122Q001F00153Q00122Q0020000A3Q00122Q002100424Q00FC001E002100022Q0033011D001D001E2Q009C011C000200022Q004D001D00033Q0020E3001D001D00342Q0046011E6Q00EE001B001E00012Q0046011B6Q0065011B00010002000657011B00970401000100040F012Q009704012Q000B012Q00014Q0046011B000A3Q001216001C004C4Q009C011B000200022Q004D001C000F3Q0020E3001D001A007F2Q0033001C00020001001288011C00243Q0020E3001D001A007F00208D001D001D00252Q00DE001D001E4Q0035011C3Q001E00040F012Q00B6040100208D002100200012001216002300394Q00FC00210023000200069A012100AC04013Q00040F012Q00AC0401001288012100383Q0006B70022000E000100012Q0046012Q00204Q003300210002000100208D002100200012001216002300374Q00FC00210023000200069A012100B504013Q00040F012Q00B50401001288012100383Q0006B70022000F000100012Q0046012Q00204Q00330021000200012Q000F001F5Q00062B001C00A30401000200040F012Q00A304012Q004D001C00103Q00069A011C00BF04013Q00040F012Q00BF0401001288011C00383Q0006B7001D0010000100012Q004D3Q00104Q0033001C00020001001288011C005A3Q00206F001C001C005B4Q001C000100024Q001D00053Q00202Q001D001D008A00062Q001D00C70401000100040F012Q00C70401001216001D00154Q0032011C001C001D000ED3001B00DF0401001C00040F012Q00DF04012Q004D001C00053Q001288011D005A3Q0020E3001D001D005B2Q0065011D0001000200105D011C008A001D001216001C008B3Q001288011D003D3Q0020E3001D001D003E2Q0046011E00183Q001216001F003F4Q00FC001D001F00022Q0087001C001C001D001288011D00383Q0006B7001E0011000100012Q0046012Q001C4Q0033001D00020001001288011D00383Q0006B7001E0012000100012Q0046012Q001C4Q0033001D000200012Q000F001C5Q00069A011B00E604013Q00040F012Q00E604012Q004D001C000D3Q001216001D00493Q001216001E005C4Q0046011F001B4Q00EE001C001F00012Q004D001C000D3Q001216001D00493Q001216001E00674Q00EE001C001E0001001288011C00033Q0020E3001C001C0004001216001D00684Q0033001C000200012Q004D001C00114Q0013011D00063Q001216001E00693Q001216001F006A3Q00121C0020006B3Q00122Q0021006C3Q00122Q0022006D3Q00122Q0023006E6Q001D000600012Q00E7001E00014Q006D011C001E000100122Q001C00033Q00202Q001C001C000400122Q001D00016Q001C000200014Q001C00056Q001D00053Q00202Q001D001D006F00062Q001D00030501000100040F012Q00030501001216001D00153Q0020AC011D001D0001001096011C006F001D4Q001C00053Q00202Q001C001C006F00122Q001D00443Q00202Q001D001D00454Q001E00163Q00202Q001E001E000500122Q001F00426Q001D001F000200062Q001D00120501001C00040F012Q001205012Q0046011C00023Q001216001D000A4Q0033001C000200012Q000B012Q00014Q000F00115Q002681010F00420501000A00040F012Q004205012Q004D001100084Q0013011200013Q0012160013008C4Q00230112000100010012160013008D4Q004601146Q0046011500014Q00FC00110015000200069A0111002305013Q00040F012Q002305012Q004D001100053Q0030930011008E00182Q000B012Q00014Q0046011100013Q0012160012008F4Q00330011000200012Q004D0011000D3Q001216001200493Q001216001300904Q00EE0011001300012Q004D0011000D3Q001216001200493Q001216001300914Q006D01110013000100122Q001100033Q00202Q00110011000400122Q001200846Q0011000200014Q001100056Q001200053Q00202Q00120012009200062Q001200380501000100040F012Q00380501001216001200153Q0020AC01120012000100105D0111009200122Q004D001100053Q0020E3001100110092000EF3000A00410501001100040F012Q004105012Q0046011100023Q001216001200424Q00330011000200012Q000B012Q00014Q0046011100044Q006501110001000200069A0111004705013Q00040F012Q004705012Q000B012Q00014Q004D001100074Q0013011200013Q001216001300934Q00230112000100012Q0013011300013Q001216001400734Q00230113000100012Q00FC0011001300022Q00D0001200113Q0026810112009E0501001500040F012Q009E050100069A0106005905013Q00040F012Q005905012Q0046011200094Q0046011300064Q009C0112000200020006570112005C0501000100040F012Q005C05012Q004D0012000E3Q001216001300944Q009C0112000200022Q004D001300094Q006501130001000200069A0112009E05013Q00040F012Q009E050100069A0113009E05013Q00040F012Q009E05012Q0062001400143Q0012880115000B3Q00208D00150015000C001216001700954Q00FC0015001700020006210016006C0501001500040F012Q006C050100208D00160015000C001216001800964Q00FC00160018000200069A0116008705013Q00040F012Q00870501001288011700243Q00208D00180016003B2Q00DE001800194Q003501173Q001900040F012Q0085050100208D001C001B0012001216001E00134Q00FC001C001E000200069A011C008505013Q00040F012Q00850501001288011C00263Q002019001C001C004D4Q001D00133Q00202Q001E001B00284Q001D0002000200122Q001E00933Q00122Q001F00016Q002000016Q001C0020000200062Q001C008505013Q00040F012Q008505010020E30014001B002E00040F012Q0087050100062B001700730501000200040F012Q0073050100068E0017008A0501001400040F012Q008A05012Q0046011700123Q0020E300180013002E2Q00320118001800170020E300180018002F000ED3005E00960501001800040F012Q009605012Q0046011800013Q001225001900976Q0018000200014Q001800086Q001900176Q0018000200016Q00014Q0046011800013Q00121B011900986Q00180002000100122Q001800033Q00202Q00180018000400122Q001900846Q0018000200016Q00014Q0046011100013Q00121B011200996Q00110002000100122Q001100033Q00202Q00110011000400122Q001200056Q0011000200016Q00013Q00133Q00053Q00030A3Q0073616265725374616765026Q00F03F03053Q00737461676503043Q006D6174682Q033Q006D617801174Q004D00015Q0020E30001000100010006572Q0100050001000100040F012Q00050001001216000100023Q0006762Q01000B00013Q00040F012Q000B00012Q004D00015Q00105D2Q0100014Q004D000100014Q00612Q01000100012Q004D000100023Q001288010200043Q0020E30002000200052Q004D000300023Q0020E3000300030003000657010300130001000100040F012Q00130001001216000300024Q004601046Q00FC00020004000200105D2Q01000300022Q000B012Q00017Q00043Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C6403053Q00536162657203083Q004261636B7061636B00104Q004D7Q0020E35Q000100069A012Q000900013Q00040F012Q0009000100208D00013Q0002001216000300034Q00FC0001000300020006572Q01000E0001000100040F012Q000E00012Q004D00015Q0020E300010001000400208D000100010002001216000300034Q00FC0001000300022Q00DA000100024Q000B012Q00017Q00103Q0003023Q006F7303053Q00636C6F636B030A3Q00626C6F636B556E74696C028Q00030B3Q00736162657265787065727403073Q00456E656D696573026Q00F03F2Q033Q0068756D2Q033Q006D646C03153Q0046696E6446697273744368696C644F66436C612Q73030A3Q00466F7263654669656C6403083Q00666967687448756D03073Q006669676874487003073Q006669676874417403063Q004865616C7468030C3Q0053616265722045787065727400453Q001294012Q00013Q00206Q00026Q000100024Q00015Q00202Q00010001000300062Q000100080001000100040F012Q00080001001216000100043Q000676012Q000C0001000100040F012Q000C00012Q00E78Q00DA3Q00024Q004D3Q00014Q00132Q0100013Q001216000200054Q00232Q01000100012Q0013010200013Q001216000300064Q00230102000100012Q00FC3Q000200022Q00D000015Q0026812Q0100190001000400040F012Q001900012Q00E700016Q00DA000100023Q0020E300013Q00070020E30002000100080020E300030001000900069A0103002600013Q00040F012Q002600010020E300030001000900208D00030003000A0012160005000B4Q00FC00030005000200069A0103002600013Q00040F012Q002600012Q00E700036Q00DA000300023Q00069A0102003700013Q00040F012Q003700012Q004D00035Q0020E300030003000C0006AD000300370001000200040F012Q003700012Q004D00036Q00BC00048Q00058Q000600023Q00202Q00070002000F00122Q000800013Q00202Q0008000800024Q00080001000200102Q0005000E000800102Q0004000D000700102Q0003000C00060006B700033Q000100032Q004D3Q00024Q0046012Q00024Q004D8Q004D000400034Q0013010500013Q001216000600054Q0023010500010001001216000600104Q0051000700036Q000800046Q000400086Q00049Q0000013Q00013Q000A3Q0003063Q004865616C746803073Q006669676874487003073Q006669676874417403023Q006F7303053Q00636C6F636B026Q002040030A3Q00626C6F636B556E74696C025Q0080564003083Q00666967687448756D2Q00374Q004D8Q0065012Q00010002000657012Q00060001000100040F012Q000600012Q00E78Q00DA3Q00024Q004D3Q00013Q00069A012Q003400013Q00040F012Q003400012Q004D3Q00013Q0020E35Q00012Q004D000100023Q0020E30001000100020006572Q0100110001000100040F012Q001100012Q004D000100013Q0020E3000100010001000676012Q001D0001000100040F012Q001D00012Q004D3Q00024Q004D000100024Q004D000200013Q0020E3000200020001001288010300043Q0020E30003000300052Q006501030001000200105D2Q010003000300105D012Q0002000200040F012Q00340001001288012Q00043Q00206F5Q00056Q000100024Q000100023Q00202Q00010001000300062Q000100270001000100040F012Q002700010012882Q0100043Q0020E30001000100052Q00652Q01000100022Q0032014Q0001000ED30006003400013Q00040F012Q003400012Q004D3Q00023Q00122A000100043Q00202Q0001000100054Q00010001000200202Q00010001000800104Q000700016Q00023Q00304Q0009000A9Q006Q00024Q00E73Q00014Q00DA3Q00024Q000B012Q00017Q000A3Q0003083Q00506F736974696F6E03093Q004D61676E6974756465025Q0070974003073Q00566563746F72332Q033Q006E6577028Q00026Q001040026Q004E4003063Q00434672616D65030A3Q0074772Q656E53702Q656401274Q004D00016Q00652Q01000100020006572Q0100060001000100040F012Q000600012Q00E700026Q00DA000200023Q0020E30002000100012Q0032010200023Q0020E3000200020002000ED3000300160001000200040F012Q001600012Q004D000200013Q001217000300043Q00202Q00030003000500122Q000400063Q00122Q000500073Q00122Q000600066Q0003000600024Q00033Q00034Q000400023Q00122Q000500086Q0002000500012Q004D000200033Q001288010300093Q0020E3000300030005001203000400043Q00202Q00040004000500122Q000500063Q00122Q000600073Q00122Q000700066Q0004000700024Q00043Q00044Q0003000200024Q000400043Q00202Q00040004000A2Q004D000500024Q0051010200054Q009101026Q000B012Q00017Q00043Q002Q033Q0049734103083Q00426173655061727403083Q00506F736974696F6E03053Q007063612Q6C01163Q000657012Q00040001000100040F012Q000400012Q0062000100014Q00DA000100023Q00208D00013Q0001001216000300024Q00FC00010003000200069A2Q01000B00013Q00040F012Q000B00010020E300013Q00032Q00DA000100023Q0012882Q0100043Q0006B700023Q000100012Q0046017Q00B200010002000200069A2Q01001300013Q00040F012Q0013000100068E000300140001000200040F012Q001400012Q0062000300034Q00DA000300024Q000B012Q00013Q00013Q00023Q0003083Q004765745069766F7403083Q00506F736974696F6E00064Q00CD7Q00206Q00016Q0002000200206Q00026Q00028Q00017Q00073Q0003093Q0043686172616374657203153Q0046696E6446697273744368696C644F66436C612Q7303083Q0048756D616E6F6964030E3Q0046696E6446697273744368696C6403083Q004261636B7061636B03063Q00506172656E7403053Q007063612Q6C01214Q004D00015Q0020E3000100010001000621000200070001000100040F012Q0007000100208D000200010002001216000400034Q00FC00020004000200069A2Q01000E00013Q00040F012Q000E000100208D0003000100042Q004601056Q00FC000300050002000657010300130001000100040F012Q001300012Q004D00035Q0020E300030003000500208D0003000300042Q004601056Q00FC00030005000200069A0103001F00013Q00040F012Q001F000100069A0102001F00013Q00040F012Q001F00010020E30004000300060006AD0004001F0001000100040F012Q001F0001001288010400073Q0006B700053Q000100022Q0046012Q00024Q0046012Q00034Q00330004000200012Q00DA000300024Q000B012Q00013Q00013Q00013Q0003093Q004571756970542Q6F6C00054Q00927Q00206Q00014Q000200018Q000200016Q00017Q00013Q0003133Q006669726570726F78696D69747970726F6D707400043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q00013Q0003113Q0066697265636C69636B6465746563746F7200043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q00043Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C642Q033Q0043757003083Q004261636B7061636B00104Q004D7Q0020E35Q000100069A012Q000900013Q00040F012Q0009000100208D00013Q0002001216000300034Q00FC0001000300020006572Q01000E0001000100040F012Q000E00012Q004D00015Q0020E300010001000400208D000100010002001216000300034Q00FC0001000300022Q00DA000100024Q000B012Q00017Q00013Q0003133Q006669726570726F78696D69747970726F6D707400043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q00013Q0003113Q0066697265636C69636B6465746563746F7200043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q00013Q0003133Q006669726570726F78696D69747970726F6D707400043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q00083Q00030C3Q0053656E644B65794576656E7403043Q00456E756D03073Q004B6579436F646503013Q004503043Q0067616D6503043Q007461736B03043Q0077616974029A5Q99B93F00174Q007F016Q00206Q00014Q000200013Q00122Q000300023Q00202Q00030003000300202Q0003000300044Q00045Q00122Q000500058Q0005000100124Q00063Q00206Q000700122Q000100088Q000200019Q0000206Q00014Q00025Q00122Q000300023Q00202Q00030003000300202Q0003000300044Q00045Q00122Q000500058Q000500016Q00017Q00043Q002Q033Q0070726903013Q007003083Q00506F736974696F6E03093Q004D61676E6974756465021B3Q0020E300023Q00010020E30003000100010006AD0002000B0001000300040F012Q000B00010020E300023Q00010020E3000300010001000639010200090001000300040F012Q000900012Q001101026Q00E7000200014Q00DA000200023Q0020E300023Q00022Q000B00035Q00202Q0003000300034Q00020002000300202Q00020002000400202Q0003000100024Q00045Q00202Q0004000400034Q00030003000400202Q00030003000400062Q000200180001000300040F012Q001800012Q001101026Q00E7000200014Q00DA000200024Q000B012Q00017Q00013Q0003113Q0066697265636C69636B6465746563746F7200043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q00013Q0003133Q006669726570726F78696D69747970726F6D707400043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q00083Q00030C3Q0053656E644B65794576656E7403043Q00456E756D03073Q004B6579436F646503013Q004503043Q0067616D6503043Q007461736B03043Q0077616974029A5Q99B93F00174Q007F016Q00206Q00014Q000200013Q00122Q000300023Q00202Q00030003000300202Q0003000300044Q00045Q00122Q000500058Q0005000100124Q00063Q00206Q000700122Q000100088Q000200019Q0000206Q00014Q00025Q00122Q000300023Q00202Q00030003000300202Q0003000300044Q00045Q00122Q000500058Q000500016Q00017Q00013Q0003043Q007761726E00043Q001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q00013Q00030C3Q00736574636C6970626F61726400073Q001288012Q00013Q00069A012Q000600013Q00040F012Q00060001001288012Q00014Q004D00016Q00333Q000200012Q000B012Q00017Q001A3Q00026Q00F03F03293Q006120517565737420646F20536567756E646F204D617220736F20657869737465206E6F20536561203103043Q007461736B03043Q0077616974027Q0040025Q00E0854003233Q007072656369736120646F206C6576656C20372Q302028766F63652065737461206E6F2003013Q0029030A3Q0069636561646D6972616C030B3Q004963652041646D6972616C03093Q00646574656374697665030A3Q006D692Q646C65746F776E03063Q006D692Q646C65030B3Q006F20446574656374697665031A3Q0066616C616E646F20636F6D206F204465746563746976653Q2E03163Q004472652Q73726F7361517565737450726F6772652Q7303093Q0044657465637469766503183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C026Q00F83F03023Q006F7303053Q00636C6F636B026Q00344003253Q0074656E74616E646F207669616A61722070617261206F20536567756E646F204D61723Q2E030F3Q0054726176656C4472652Q73726F7361026Q00084002614Q004D00026Q00610102000100012Q004D000200013Q00267B0002000D0001000100040F012Q000D00012Q0046010200013Q00121B010300026Q00020002000100122Q000200033Q00202Q00020002000400122Q000300056Q0002000200016Q00014Q004D000200024Q00650102000100020026950002001D0001000600040F012Q001D00012Q0046010200013Q001206000300076Q000400026Q00040001000200122Q000500086Q0003000300054Q00020002000100122Q000200033Q00202Q00020002000400122Q000300056Q0002000200016Q00014Q004D000200034Q0013010300013Q001216000400094Q00230103000100010012160004000A4Q004601056Q0046010600014Q00FC00020006000200069A0102002800013Q00040F012Q002800012Q000B012Q00014Q004D000200044Q0013010300013Q0012160004000B4Q00230103000100012Q0013010400023Q0012160005000C3Q0012160006000D4Q00230104000200012Q004601056Q0046010600013Q0012160007000E4Q00FC00020007000200069A0102003A00013Q00040F012Q003A00012Q004601036Q00650103000100020006570103003B0001000100040F012Q003B00012Q000B012Q00014Q0046010300013Q0012160004000F4Q00330003000200012Q004D000300053Q001216000400103Q001216000500114Q00EE0003000500012Q004D000300063Q00208D000400020012001216000600134Q00A1010400064Q00F700033Q0001001288010300033Q0020E3000300030004001216000400144Q0033000300020001001288010300153Q0020500003000300164Q0003000100024Q000400076Q000300030004000E2Q0017005C0001000300040F012Q005C0001001288010300153Q0020E30003000300162Q00650103000100022Q00B8000300074Q0046010300013Q001216000400184Q00330003000200012Q004D000300053Q001216000400194Q0033000300020001001288010300033Q0020E30003000300040012160004001A4Q00330003000200012Q000B012Q00017Q00143Q00027Q0040032A3Q006120517565737420646F20546572636569726F204D617220736F20657869737465206E6F20536561203203043Q007461736B03043Q0077616974025Q0070974003243Q007072656369736120646F206C6576656C2031352Q302028766F63652065737461206E6F2003013Q002903073Q00646F6E7377616E03083Q00446F6E205377616E03223Q00706567616E646F206120717565737420646F20546572636569726F204D61723Q2E030E3Q005A517565737450726F6772652Q7303053Q00436865636B03053Q00426567696E026Q00F83F03023Q006F7303053Q00636C6F636B026Q00344003263Q0074656E74616E646F207669616A61722070617261206F20546572636569726F204D61723Q2E03093Q0054726176656C5A6F75026Q000840024D4Q004D00026Q00610102000100012Q004D000200013Q00267B0002000D0001000100040F012Q000D00012Q0046010200013Q00121B010300026Q00020002000100122Q000200033Q00202Q00020002000400122Q000300016Q0002000200016Q00014Q004D000200024Q00650102000100020026950002001D0001000500040F012Q001D00012Q0046010200013Q001206000300066Q000400026Q00040001000200122Q000500076Q0003000300054Q00020002000100122Q000200033Q00202Q00020002000400122Q000300016Q0002000200016Q00014Q004D000200034Q0013010300013Q001216000400084Q0023010300010001001216000400094Q004601056Q0046010600014Q00FC00020006000200069A0102002800013Q00040F012Q002800012Q000B012Q00014Q0046010200013Q0012160003000A4Q00330002000200012Q004D000200043Q0012160003000B3Q0012160004000C4Q00EE0002000400012Q004D000200043Q0012160003000B3Q0012160004000D4Q00EE000200040001001288010200033Q0020E30002000200040012160003000E4Q00330002000200010012880102000F3Q0020500002000200104Q0002000100024Q000300056Q000200020003000E2Q001100480001000200040F012Q004800010012880102000F3Q0020E30002000200102Q00650102000100022Q00B8000200054Q0046010200013Q001216000300124Q00330002000200012Q004D000200043Q001216000300134Q0033000200020001001288010200033Q0020E3000200020004001216000300144Q00330002000200012Q000B012Q00017Q00033Q0003013Q003F026Q00F03F03053Q007063612Q6C00103Q0012163Q00013Q001216000100023Q001288010200033Q0006B700033Q000100022Q0046017Q004D8Q0033000200020001001288010200033Q0006B700030001000100022Q004D8Q0046012Q00014Q00330002000200012Q004601026Q0046010300014Q0036000200034Q000B012Q00013Q00023Q00043Q0003083Q00746F737472696E6703043Q004461746103043Q005261636503053Q0056616C756500083Q001288012Q00014Q004D000100013Q0020E30001000100020020E30001000100030020E30001000100042Q009C012Q000200022Q00B88Q000B012Q00017Q00053Q0003043Q004461746103043Q0052616365030E3Q0046696E6446697273744368696C6403073Q0045766F6C766564027Q0040000B4Q0034016Q00206Q000100206Q000200206Q000300122Q000200048Q0002000200064Q000A00013Q00040F012Q000A00010012163Q00054Q00B83Q00014Q000B012Q00017Q000C3Q00028Q0003063Q0069706169727303083Q004261636B7061636B03093Q00436861726163746572030B3Q004765744368696C6472656E2Q033Q0049734103043Q00542Q6F6C03063Q00737472696E6703043Q0066696E6403043Q004E616D6503063Q00666C6F776572026Q00F03F00283Q0012163Q00013Q0012882Q0100024Q0013010200024Q004D00035Q0020E30003000300032Q004D00045Q0020E30004000400042Q00230102000200012Q00B200010002000300040F012Q0024000100069A0105002400013Q00040F012Q00240001001288010600023Q00208D0007000500052Q00DE000700084Q003501063Q000800040F012Q0022000100208D000B000A0006001216000D00074Q00FC000B000D000200069A010B002200013Q00040F012Q00220001001288010B00083Q002019000B000B00094Q000C00013Q00202Q000D000A000A4Q000C0002000200122Q000D000B3Q00122Q000E000C6Q000F00016Q000B000F000200062Q000B002200013Q00040F012Q002200010020AC014Q000C00062B000600110001000200040F012Q0011000100062B0001000A0001000200040F012Q000A00012Q00DA3Q00024Q000B012Q00017Q00043Q0003063Q0072616365563203063Q0072616365563303083Q00612Q636570746564010001073Q00267B3Q00040001000100040F012Q00040001002681012Q00060001000200040F012Q000600012Q004D00015Q0030930001000300042Q000B012Q00017Q002C3Q00027Q0040030E3Q00206A612065737461206E6120563203063Q0072616365563203213Q00612056322065206665697461206E6F2053656120322028416C6368656D6973742903043Q007461736B03043Q0077616974025Q00908A4003143Q007072656369736120646F206C6576656C20383530026Q00084003093Q00616C6368656D69737403093Q0067722Q656E7A6F6E6503053Q0067722Q656E030B3Q006F20416C6368656D69737403173Q00656E74726567616E646F20617320666C6F7265733Q2E03093Q00416C6368656D69737403013Q003303083Q00612Q636570746564031F3Q00706567616E646F206120717565737420646F20416C6368656D6973743Q2E03013Q003103013Q003203183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C2Q01026Q00F83F026Q00F03F03093Q00776F726B7370616365030E3Q0046696E6446697273744368696C6403063Q00466C6F77657203113Q00636F6C6574616E646F206120666C6F722003023Q0020282Q033Q002F332903063Q00434672616D652Q033Q006E657703083Q00506F736974696F6E03073Q00566563746F7233028Q00030A3Q0074772Q656E53702Q656403343Q00616775617264616E646F20617320666C6F7265732028617A756C203D206E6F6974652C207665726D656C6861203D20646961292003143Q002F33207C206661726D616E646F207A756D626973030A3Q00726163655A6F6D62696503083Q0075736551756573742Q033Q006C6F6303093Q0067726176657961726403063Q0066696C74657202C34Q006301028Q0002000100014Q000200016Q000200010003000E2Q000100100001000300040F012Q001000012Q0046010400014Q0046010500023Q001216000600024Q00870005000500062Q00330004000200012Q004D000400023Q001216000500034Q00E700066Q00EE0004000600012Q000B012Q00014Q004D000400033Q00267B0004001B0001000100040F012Q001B00012Q0046010400013Q00121B010500046Q00040002000100122Q000400053Q00202Q00040004000600122Q000500016Q0004000200016Q00014Q004D000400044Q0065010400010002002695000400270001000700040F012Q002700012Q0046010400013Q00121B010500086Q00040002000100122Q000400053Q00202Q00040004000600122Q000500016Q0004000200016Q00014Q004D000400054Q0065010400010002000EF30009004A0001000400040F012Q004A00012Q004D000500064Q0013010600013Q0012160007000A4Q00230106000100012Q0013010700023Q0012160008000B3Q0012160009000C4Q00230107000200012Q004601086Q0046010900013Q001216000A000D4Q00FC0005000A000200069A0105003D00013Q00040F012Q003D00012Q004601066Q00650106000100020006570106003E0001000100040F012Q003E00012Q000B012Q00014Q0046010600013Q0012160007000E4Q00330006000200012Q004D000600073Q0012160007000F3Q001216000800104Q00EE000600080001001288010600053Q0020E3000600060006001216000700014Q00330006000200012Q000B012Q00014Q004D000500083Q0020E3000500050011000657010500780001000100040F012Q007800012Q004D000500064Q0013010600013Q0012160007000A4Q00230106000100012Q0013010700023Q0012160008000B3Q0012160009000C4Q00230107000200012Q004601086Q0046010900013Q001216000A000D4Q00FC0005000A000200069A0105006000013Q00040F012Q006000012Q004601066Q0065010600010002000657010600610001000100040F012Q006100012Q000B012Q00014Q0046010600013Q001238010700126Q0006000200014Q000600073Q00122Q0007000F3Q00122Q000800136Q0006000800014Q000600073Q00122Q0007000F3Q00122Q000800146Q0006000800014Q000600093Q00202Q00070005001500122Q000900166Q000700096Q00063Q00014Q000600083Q00302Q00060011001700122Q000600053Q00202Q00060006000600122Q000700186Q0006000200016Q00013Q001216000500193Q001216000600093Q001216000700193Q000463000500AF00010012880109001A3Q00209301090009001B00122Q000B001C6Q000C00086Q000B000B000C4Q0009000B000200062Q000A00870001000900040F012Q008700012Q004D000A000A4Q0046010B00094Q009C010A0002000200069A010A00AE00013Q00040F012Q00AE00012Q0046010B00013Q0012D7000C001D6Q000D00083Q00122Q000E001E6Q000F00043Q00122Q0010001F6Q000C000C00104Q000B000200014Q000B000B3Q00122Q000C00203Q00202Q000C000C00210020E3000D000A0022001203000E00233Q00202Q000E000E002100122Q000F00243Q00122Q001000093Q00122Q001100246Q000E001100024Q000D000D000E4Q000C000200024Q000D000C3Q00202Q000D000D00252Q0046010E6Q00FC000B000E000200069A010B00AD00013Q00040F012Q00AD00012Q004D000B000D4Q003B000C000A6Q000B000200014Q000B00096Q000C00096Q000B0002000100122Q000B00053Q00202Q000B000B000600122Q000C00196Q000B000200012Q000B012Q00013Q0004060105007C00012Q0046010500013Q001216000600264Q0046010700043Q001216000800274Q00870006000600082Q00330005000200012Q000E0105000E3Q00122Q000600286Q00073Q000300302Q0007002900174Q000800013Q00122Q0009002B6Q00080001000100105D0107002A000800028500085Q00104E0007002C00084Q00088Q000900016Q0005000900016Q00013Q00013Q00013Q0003063Q007A6F6D62696501063Q00267B3Q00030001000100040F012Q000300012Q00112Q016Q00E7000100014Q00DA000100024Q000B012Q00017Q00183Q00027Q004003143Q003A20666163612061205632207072696D6569726F03043Q007461736B03043Q0077616974030B3Q0077656E6C6F636B746F616403073Q0077656E6C6F636B03453Q0056333A206E616F206163686569206F204E50432057656E6C6F636B746F61642E2056612061746520656C6520756D612076657A20286F20736372697074206772617661292E026Q00084003083Q00506F736974696F6E03093Q004D61676E6974756465026Q00344003193Q00696E646F20617465206F2057656E6C6F636B746F61643Q2E03063Q00434672616D652Q033Q006E657703073Q00566563746F7233028Q00026Q001040030A3Q0074772Q656E53702Q6564030B3Q0057656E6C6F636B746F616403013Q003103183Q0046696E644669727374416E636573746F724F66436C612Q7303053Q004D6F64656C03313Q0066616C656920636F6D206F2057656E6C6F636B746F61642E20436F6E636C7561206F20747269616C20646120726163612003193Q0020286F206A6F676F20677569612070656C612074656C61292E02504Q004D00026Q00B10002000100030026950003000E0001000100040F012Q000E00012Q0046010400014Q0046010500023Q001216000600024Q00870005000500062Q0033000400020001001288010400033Q0020E3000400040004001216000500014Q00330004000200012Q000B012Q00014Q004D000400014Q0013010500023Q001216000600053Q001216000700064Q00230105000200012Q009C0104000200020006570104001E0001000100040F012Q001E00012Q0046010500013Q00121B010600076Q00050002000100122Q000500033Q00202Q00050005000400122Q000600086Q0005000200016Q00014Q004D000500024Q006501050001000200069A0105003C00013Q00040F012Q003C00010020E30006000500090020E30007000400092Q00320106000600070020E300060006000A000ED3000B003C0001000600040F012Q003C00012Q0046010600013Q0012380007000C6Q0006000200014Q000600033Q00122Q0007000D3Q00202Q00070007000E00202Q00080004000900122Q0009000F3Q00202Q00090009000E00122Q000A00103Q00122Q000B00083Q00122Q000C00116Q0009000C00024Q0008000800094Q0007000200024Q000800043Q00202Q0008000800124Q00098Q0006000900016Q00014Q004D000600053Q001207010700133Q00122Q000800146Q0006000800014Q000600063Q00202Q00070004001500122Q000900166Q000700096Q00063Q00014Q000600013Q00122Q000700176Q000800023Q00122Q000900186Q0007000700094Q00060002000100122Q000600033Q00202Q00060006000400122Q000700116Q0006000200016Q00017Q00023Q0003093Q006D6963726F636869702Q000B4Q004D8Q00132Q0100013Q001216000200014Q00232Q01000100012Q009C012Q00020002002681012Q00080001000200040F012Q000800012Q0011017Q00E73Q00014Q00DA3Q00024Q000B012Q00017Q000D3Q0003063Q00697061697273030B3Q004765744368696C6472656E03063Q00737472696E6703053Q006D6174636803043Q004E616D65030C3Q005E49736C616E64202825642903053Q007063612Q6C03053Q007461626C6503063Q00696E736572742Q033Q006E756D03083Q00746F6E756D6265722Q033Q00706F7303043Q00736F7274002C4Q0013017Q004D00016Q00652Q01000100020006572Q0100060001000100040F012Q000600012Q00DA3Q00023Q001288010200013Q00208D0003000100022Q00DE000300044Q003501023Q000400040F012Q00230001001288010700033Q0020E30007000700040020E3000800060005001216000900064Q00FC00070009000200069A0107002200013Q00040F012Q00220001001288010800073Q0006B700093Q000100012Q0046012Q00064Q00B200080002000900069A0108002200013Q00040F012Q00220001001288010A00083Q0020E3000A000A00092Q0046010B6Q0013010C3Q0002001288010D000B4Q0046010E00074Q009C010D0002000200105D010C000A000D00105D010C000C00092Q00EE000A000C00012Q000F00055Q00062B0002000B0001000200040F012Q000B0001001288010200083Q0020E300020002000D2Q004601035Q000285000400014Q00EE0002000400012Q00DA3Q00024Q000B012Q00013Q00023Q00023Q0003083Q004765745069766F7403083Q00506F736974696F6E00064Q00CD7Q00206Q00016Q0002000200206Q00026Q00028Q00017Q00013Q002Q033Q006E756D02083Q0020E300023Q00010020E3000300010001000639010300050001000200040F012Q000500012Q001101026Q00E7000200014Q00DA000200024Q000B012Q00017Q00013Q00029Q00094Q004D8Q0065012Q000100022Q00D07Q000EA72Q01000600013Q00040F012Q000600012Q0011017Q00E73Q00014Q00DA3Q00024Q000B012Q00017Q00023Q0003063Q00697061697273025Q00C0584000203Q001297010200016Q00038Q000300016Q00023Q000400044Q001600012Q004D000700014Q004D000800024Q004D000900034Q0046010A00064Q00DE0009000A4Q000400083Q00022Q00730007000700080006570107000F0001000100040F012Q000F0001001216000700023Q00069A2Q01001300013Q00040F012Q00130001000676010700160001000100040F012Q001600012Q0046010800064Q00462Q0100074Q0046012Q00083Q00062B000200050001000200040F012Q0005000100069A012Q001D00013Q00040F012Q001D00010026950001001D0001000200040F012Q001D00012Q00DA3Q00024Q0062000200024Q00DA000200024Q000B012Q00017Q00013Q0003073Q006275794368697000104Q004D7Q0020E35Q000100069A012Q000E00013Q00040F012Q000E00012Q004D3Q00014Q0065012Q00010002000657012Q000C0001000100040F012Q000C00012Q004D3Q00024Q0065012Q000100022Q00A77Q00040F012Q000E00012Q0011017Q00E73Q00014Q00DA3Q00024Q000B012Q00017Q00173Q00026Q00F03F03213Q00726169647320736F206578697374656D206E6F205365612032206520536561203303043Q007461736B03043Q0077616974027Q004003133Q006D7973746572696F752Q736369656E7469737403093Q00736369656E74697374030E3Q00636173746C656F6E746865736561030A3Q00686F74616E64636F6C6403063Q00636173746C6503163Q006F204369656E7469737461204D6973746572696F736F03083Q006261644672756974031C3Q007573616E646F2061206672757461206D616973206261726174612028030D3Q00292070617261206F2063686970026Q33E33F03113Q00636F6D7072616E646F206F20636869702003083Q0072616964547970652Q033Q003Q2E03083Q0052616964734E706303063Q0053656C656374030E3Q006368697020636F6D707261646F21032D3Q006E616F20636F6E736567756920636F6D70726172206F2063686970202873656D2062656C692F66727574613F29026Q001040025A4Q004D00026Q00610102000100012Q004D000200013Q0026810102000D0001000100040F012Q000D00012Q0046010200013Q00121B010300026Q00020002000100122Q000200033Q00202Q00020002000400122Q000300056Q0002000200016Q00014Q004D000200024Q0013010300023Q001216000400063Q001216000500074Q00230103000200012Q0013010400033Q001216000500083Q001216000600093Q0012160007000A4Q00230104000300012Q004601056Q0046010600013Q0012160007000B4Q00FC00020007000200069A0102002100013Q00040F012Q002100012Q004601036Q0065010300010002000657010300220001000100040F012Q002200012Q000B012Q00014Q004D000300033Q0020E300030003000C00069A0103003900013Q00040F012Q003900012Q004D000300044Q006501030001000200069A0103003900013Q00040F012Q003900012Q0046010400013Q0012160005000D4Q004D000600054Q0046010700034Q009C0106000200020012160007000E4Q00870005000500072Q00330004000200012Q004D000400064Q0046010500034Q0033000400020001001288010400033Q0020E30004000400040012160005000F4Q00330004000200012Q0046010300013Q001216000400104Q004D000500033Q0020E3000500050011001216000600124Q00870004000400062Q00330003000200012Q004D000300073Q001216000400133Q001216000500144Q004D000600033Q0020E30006000600112Q00EE000300060001001288010300033Q0020E3000300030004001216000400054Q00330003000200012Q004D000300084Q006501030001000200069A0103005200013Q00040F012Q005200012Q0046010300013Q001216000400154Q003300030002000100040F012Q005900012Q0046010300013Q001216000400164Q0033000300020001001288010300033Q0020E3000300030004001216000400174Q00330003000200012Q000B012Q00017Q00013Q0003073Q006275794368697000044Q004D7Q0020E35Q00012Q00DA3Q00024Q000B012Q00017Q000E3Q0003063Q00506172656E7403093Q00776F726B7370616365030E3Q0046696E6446697273744368696C642Q033Q004D617003063Q00697061697273030E3Q0047657444657363656E64616E74732Q033Q00497341030D3Q00436C69636B4465746563746F7203063Q00737472696E6703053Q006C6F776572030B3Q0047657446752Q6C4E616D6503043Q0066696E64030A3Q007261696473752Q6D6F6E026Q00F03F003A4Q004D7Q00069A012Q000900013Q00040F012Q000900012Q004D7Q0020E35Q000100069A012Q000900013Q00040F012Q000900012Q004D8Q00DA3Q00023Q001288012Q00023Q00208D5Q0003001216000200044Q00FC3Q00020002000657012Q00110001000100040F012Q001100012Q0062000100014Q00DA000100023Q0012882Q0100053Q00208D00023Q00062Q00DE000200034Q00352Q013Q000300040F012Q0035000100208D000600050007001216000800084Q00FC00060008000200069A0106003500013Q00040F012Q003500010020E300060005000100069A0106002500013Q00040F012Q002500010020E30006000500010020E300060006000100069A0106002500013Q00040F012Q002500010020E30006000500010020E30006000600010020E3000600060001001288010700093Q00202D00070007000A00202Q00080005000B4Q000800096Q00073Q000200122Q000800093Q00202Q00080008000C4Q000900073Q00122Q000A000D3Q00122Q000B000E6Q000C00016Q0008000C000200062Q0008003500013Q00040F012Q003500012Q00B800056Q00DA000500023Q00062B000100160001000200040F012Q001600012Q0062000100014Q00DA000100024Q000B012Q00019Q003Q00084Q004D8Q0065012Q00010002000657012Q00060001000100040F012Q000600012Q004D3Q00014Q0065012Q000100022Q00DA3Q00024Q000B012Q00017Q001D3Q00034Q0003073Q00456E656D696573028Q00030F3Q00526169643A206C7574616E646F2028030D3Q0020696E696D69676F7329207C20030A3Q0074772Q656E53702Q6564026Q002E40026Q00F03F03173Q00526169643A20696E646F2070617261206120696C6861202Q033Q006E756D03063Q00434672616D652Q033Q006E65772Q033Q00706F7303073Q00566563746F7233026Q00444003043Q007461736B03043Q0077616974026Q00E03F03453Q00626F74616F20646520696E696369617220612072616964206E616F20656E636F6E747261646F2028766120617465206F206C61626F7261746F72696F206465207261696429026Q00084003063Q00506172656E742Q033Q0049734103083Q00426173655061727403083Q00506F736974696F6E031B3Q00696E646F20617465206F20626F74616F20646120726169643Q2E026Q00104003133Q00696E696369616E646F206120726169643Q2E03113Q0066697265636C69636B6465746563746F7203053Q007063612Q6C027F4Q004D00026Q006501020001000200069A0102004400013Q00040F012Q004400012Q004D000200014Q0013010300013Q001216000400014Q00230103000100012Q0013010400013Q001216000500024Q00230104000100012Q00FC0002000400022Q00D0000300023Q000ED3000300250001000300040F012Q002500012Q004D000300024Q0009000400026Q0003000200044Q000500013Q00122Q000600046Q000700023Q00122Q000800056Q000900036Q0009000100024Q0006000600094Q0005000200014Q000500046Q000600036Q00078Q000800056Q0008000100024Q00098Q000A00063Q00202Q000A000A000600122Q000B00076Q0005000B000100044Q004300012Q004D000300074Q00650103000100020020E300030003000800069A0103003F00013Q00040F012Q003F00012Q0046010400013Q001216000500093Q0020E300060003000A2Q00870005000500062Q00740004000200014Q000400083Q00122Q0005000B3Q00202Q00050005000C00202Q00060003000D00122Q0007000E3Q00202Q00070007000C00122Q000800033Q00122Q0009000F3Q00122Q000A00034Q00FC0007000A00022Q00330106000600072Q009C0105000200022Q004D000600063Q0020E30006000600062Q004601076Q00EE000400070001001288010400103Q0020E3000400040011001216000500124Q00330004000200012Q000B012Q00014Q004D000200094Q0065010200010002000657010200500001000100040F012Q005000012Q0046010300013Q00121B010400136Q00030002000100122Q000300103Q00202Q00030003001100122Q000400146Q0003000200016Q00013Q0020E3000300020015000621000400590001000300040F012Q0059000100208D000400030016001216000600174Q00FC00040006000200069A0104005900013Q00040F012Q005900010020E300040003001800069A0104007000013Q00040F012Q007000012Q0046010500013Q001290000600196Q0005000200014Q000500083Q00122Q0006000B3Q00202Q00060006000C00122Q0007000E3Q00202Q00070007000C00122Q000800033Q00122Q000900143Q00122Q000A001A6Q0007000A00024Q0007000400074Q0006000200024Q000700063Q00202Q0007000700064Q00088Q00050008000200062Q000500700001000100040F012Q007000012Q000B012Q00014Q0046010500013Q0012160006001B4Q00330005000200010012880105001C3Q00069A0105007A00013Q00040F012Q007A00010012880105001D3Q0012880106001C4Q0046010700024Q00EE000500070001001288010500103Q0020E3000500050011001216000600144Q00330005000200012Q000B012Q00017Q00013Q0003063Q006177616B656E00044Q004D7Q0020E35Q00012Q00DA3Q00024Q000B012Q00017Q000C3Q00032D3Q0074656E74616E646F2064657370657274617220617320686162696C6964616465732064612066727574613Q2E03083Q004177616B656E657203053Q00436865636B03043Q007461736B03043Q0077616974026Q00F03F03063Q004177616B656E03123Q00726573706F73746120646F206A6F676F3A2003083Q00746F737472696E672Q033Q00202F20032B3Q0020287072656369736120657374617220706572746F20646F204D7973746572696F757320456E746974792903063Q006177616B656E02204Q00AA010200013Q00122Q000300016Q0002000200014Q00025Q00122Q000300023Q00122Q000400036Q00020004000200122Q000300043Q00202Q00030003000500122Q000400064Q00330003000200012Q004D00035Q001216000400023Q001216000500074Q00FC0003000500022Q0046010400013Q001216000500083Q001288010600094Q0046010700024Q009C0106000200020012160007000A3Q001288010800094Q0046010900034Q009C0108000200020012160009000B4Q00870005000500092Q00330004000200012Q004D000400013Q0012160005000C4Q00E700066Q00EE0004000600012Q000B012Q00017Q00073Q0003063Q00506172656E7403053Q00616374563303053Q00616374563403053Q007063612Q6C03043Q007461736B03043Q0077616974026Q00F03F001A4Q004D7Q000657012Q00190001000100040F012Q001900012Q004D3Q00013Q0020E35Q000100069A012Q001900013Q00040F012Q001900012Q004D3Q00023Q0020E35Q0002000657012Q000F0001000100040F012Q000F00012Q004D3Q00023Q0020E35Q000300069A012Q001400013Q00040F012Q00140001001288012Q00043Q0006B700013Q000100022Q004D3Q00034Q004D3Q00044Q00333Q00020001001288012Q00053Q0020E35Q0006001216000100074Q00333Q0002000100040F014Q00012Q000B012Q00013Q00013Q000E3Q0003093Q00436861726163746572030E3Q0046696E6446697273744368696C64030A3Q0052616365456E65726779030F3Q00526163655472616E73666F726D656403053Q0056616C756502AE47E17A14AEEF3F030C3Q0053656E644B65794576656E7403043Q00456E756D03073Q004B6579436F646503013Q005903043Q0067616D6503043Q007461736B03043Q0077616974029A5Q99B93F00304Q004D7Q0020E35Q00010006210001000700013Q00040F012Q0007000100208D00013Q0002001216000300034Q00FC0001000300020006210002000C00013Q00040F012Q000C000100208D00023Q0002001216000400044Q00FC00020004000200069A2Q01002F00013Q00040F012Q002F00010020E3000300010005000EF30006002F0001000300040F012Q002F000100069A0102001600013Q00040F012Q001600010020E30003000200050006570103002F0001000100040F012Q002F00012Q004D000300013Q00069A0103002F00013Q00040F012Q002F00012Q004D000300013Q00208D0003000300072Q00E7000500013Q001288010600083Q0020E30006000600090020E300060006000A2Q00E700075Q0012880108000B4Q00EE0003000800010012880103000C3Q0020E300030003000D0012160004000E4Q00330003000200012Q004D000300013Q00208D0003000300072Q00E700055Q001288010600083Q0020E30006000600090020E300060006000A2Q00E700075Q0012880108000B4Q00EE0003000800012Q000B012Q00017Q00013Q0003053Q007063612Q6C00053Q001288012Q00013Q0006B700013Q000100012Q004D8Q00333Q000200012Q000B012Q00013Q00013Q00043Q0003113Q0043617074757265436F6E74726F2Q6C6572030C3Q00436C69636B42752Q746F6E3203073Q00566563746F72322Q033Q006E6577000A4Q004D7Q00208D5Q00012Q00333Q000200012Q004D7Q00208D5Q0002001288010200033Q0020E30002000200042Q0077010200014Q00F75Q00012Q000B012Q00017Q000A3Q0003023Q006F7303053Q00636C6F636B03063Q00506172656E742Q033Q0061666B03063Q0061666B4D696E026Q004E4003053Q007063612Q6C03043Q007461736B03043Q0077616974027Q004000273Q001288012Q00013Q0020E35Q00022Q0065012Q000100022Q004D00015Q0006572Q0100260001000100040F012Q002600012Q004D000100013Q0020E300010001000300069A2Q01002600013Q00040F012Q002600012Q004D000100023Q0020E300010001000400069A2Q01002100013Q00040F012Q002100010012882Q0100013Q0020E30001000100022Q00652Q01000100022Q00322Q0100014Q004D000200023Q0020E30002000200050020AF0102000200060006F2000200210001000100040F012Q002100010012882Q0100013Q0020E30001000100022Q00652Q01000100022Q0046012Q00013Q0012882Q0100073Q0006B700023Q000100032Q004D3Q00034Q004D3Q00044Q004D3Q00054Q00330001000200010012882Q0100083Q0020E30001000100090012160002000A4Q003300010002000100040F012Q000300012Q000B012Q00013Q00013Q00083Q0003113Q0043617074757265436F6E74726F2Q6C6572030C3Q00436C69636B42752Q746F6E3103073Q00566563746F72322Q033Q006E6577027Q004003123Q0053656E644D6F7573654D6F76654576656E74026Q00084003043Q0067616D6500174Q00E67Q00206Q00016Q000200019Q0000206Q000200122Q000200033Q00202Q00020002000400122Q000300053Q00122Q000400056Q000200044Q00F75Q00012Q004D3Q00013Q00069A012Q001600013Q00040F012Q001600012Q004D3Q00024Q00B13Q000100012Q004D000200013Q00208D0002000200060020AC01043Q00070020AC010500010007001288010600084Q00EE0002000600012Q000B012Q00017Q002B3Q0003093Q0077616C6B576174657203073Q0044657374726F7903043Q005061727403043Q0053697A6503073Q00566563746F72332Q033Q006E6577026Q003A40027Q0040030C3Q005472616E73706172656E6379026Q00F03F03083Q00416E63686F7265642Q01030A3Q0043616E436F2Q6C69646503083Q0043616E5175657279010003083Q0043616E546F75636803043Q004E616D65030A3Q004F72696F6E576174657203093Q00776F726B7370616365030D3Q0052617963617374506172616D73030A3Q0046696C7465725479706503043Q00456E756D03113Q005261796361737446696C7465725479706503073Q004578636C756465031A3Q0046696C74657244657363656E64616E7473496E7374616E63657303093Q00436861726163746572030B3Q0049676E6F7265576174657203073Q005261796361737403083Q00506F736974696F6E028Q00026Q0030C003083Q004D6174657269616C03053Q00576174657203063Q00737472696E6703043Q0066696E6403053Q006C6F77657203083Q00496E7374616E636503053Q00776174657203063Q00434672616D6503013Q005803013Q005903013Q005A025Q0088C3C0006F4Q004D7Q0020E35Q0001000657012Q000D0001000100040F012Q000D00012Q004D3Q00013Q00069A012Q000C00013Q00040F012Q000C00012Q004D3Q00013Q00208D5Q00022Q00333Q000200012Q00628Q00B83Q00014Q000B012Q00014Q004D3Q00024Q0065012Q00010002000657012Q00120001000100040F012Q001200012Q000B012Q00014Q004D000100013Q0006572Q0100280001000100040F012Q002800012Q004D000100033Q00122F000200036Q00033Q000700122Q000400053Q00202Q00040004000600122Q000500073Q00122Q000600083Q00122Q000700076Q00040007000200102Q00030004000400302Q00030009000A0030930003000B000C0030930003000D000C0030930003000E000F00309300030010000F003093000300110012001288010400134Q00FC0001000400022Q00B8000100013Q0012882Q0100143Q0020E30001000100062Q00652Q0100010002001288010200163Q0020E30002000200170020E300020002001800105D2Q01001500022Q0013010200024Q004D000300043Q0020E300030003001A2Q004D000400014Q002301020002000100105D2Q010019000200303D2Q01001B000F00122Q000200133Q00202Q00020002001C00202Q00043Q001D00122Q000500053Q00202Q00050005000600122Q0006001E3Q00122Q0007001F3Q00122Q0008001E6Q0005000800024Q000600016Q00020006000200062Q000300570001000200040F012Q005700010020E3000300020020001288010400163Q0020E30004000400200020E30004000400210006AD000300560001000400040F012Q00560001001288010300223Q0020E3000300030023001288010400223Q0020E30004000400240020E30005000200250020E30005000500112Q009C010400020002001216000500263Q0012160006000A4Q00E7000700014Q00FC00030007000200040F012Q005700012Q001101036Q00E7000300013Q00069A0103006600013Q00040F012Q006600012Q004D000400013Q001288010500273Q0020E30005000500060020E300060002001D0020E30006000600280020E300070002001D0020E300070007002900207800070007000A0020E300080002001D0020E300080008002A2Q00FC00050008000200105D01040027000500040F012Q006E00012Q004D000400013Q001288010500273Q0020E30005000500060012160006001E3Q0012160007002B3Q0012160008001E4Q00FC00050008000200105D0104002700052Q000B012Q00017Q00083Q002Q033Q00497341030F3Q005061727469636C65456D692Q74657203053Q00547261696C03043Q004265616D03053Q00536D6F6B6503043Q004669726503083Q00537061726B6C657303053Q007063612Q6C01233Q00208D00013Q0001001216000300024Q00FC0001000300020006572Q01001E0001000100040F012Q001E000100208D00013Q0001001216000300034Q00FC0001000300020006572Q01001E0001000100040F012Q001E000100208D00013Q0001001216000300044Q00FC0001000300020006572Q01001E0001000100040F012Q001E000100208D00013Q0001001216000300054Q00FC0001000300020006572Q01001E0001000100040F012Q001E000100208D00013Q0001001216000300064Q00FC0001000300020006572Q01001E0001000100040F012Q001E000100208D00013Q0001001216000300074Q00FC00010003000200069A2Q01002200013Q00040F012Q002200010012882Q0100083Q0006B700023Q000100012Q0046017Q00330001000200012Q000B012Q00013Q00013Q00023Q0003073Q00456E61626C6564012Q00034Q004D7Q0030933Q000100022Q000B012Q00017Q00063Q0003053Q007063612Q6C03093Q00776F726B7370616365030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E65637403043Q007461736B03053Q00737061776E001D3Q001288012Q00013Q00028500016Q00333Q00020001001288012Q00013Q0006B700010001000100012Q004D8Q00333Q000200012Q004D3Q00013Q000657012Q00150001000100040F012Q001500012Q00E73Q00014Q008E012Q00018Q00023Q00122Q000100023Q00202Q00010001000300202Q0001000100040006B700030002000100022Q004D3Q00034Q004D3Q00044Q00A12Q0100034Q00F75Q0001001288012Q00053Q0020E35Q00060006B700010003000100032Q004D3Q00044Q004D3Q00034Q004D3Q00054Q00333Q000200012Q000B012Q00013Q00043Q00053Q0003083Q0073652Q74696E677303093Q0052656E646572696E67030C3Q005175616C6974794C6576656C03043Q00456E756D03073Q004C6576656C303100083Q00128A012Q00018Q0001000200206Q000200122Q000100043Q00202Q00010001000300202Q00010001000500104Q000300016Q00017Q00113Q00030D3Q00476C6F62616C536861646F7773010003063Q00466F67456E64023Q00C088C3004203063Q00697061697273030B3Q004765744368696C6472656E2Q033Q00497341030A3Q00506F7374452Q66656374030A3Q0041746D6F73706865726503073Q0044657374726F7903093Q00776F726B737061636503153Q0046696E6446697273744368696C644F66436C612Q7303073Q0054652Q7261696E030D3Q0057617465725761766553697A65028Q00030E3Q0057617465725761766553702Q656403103Q0057617465725265666C656374616E636500224Q0044016Q00304Q000100029Q0000304Q0003000400124Q00056Q00015Q00202Q0001000100064Q000100029Q00000200044Q0016000100208D000500040007001216000700084Q00FC000500070002000657010500140001000100040F012Q0014000100208D000500040007001216000700094Q00FC00050007000200069A0105001600013Q00040F012Q0016000100208D00050004000A2Q003300050002000100062B3Q000A0001000200040F012Q000A0001001288012Q000B3Q00208D5Q000C0012160002000D4Q00FC3Q0002000200069A012Q002100013Q00040F012Q002100010030933Q000E000F0030933Q0010000F0030933Q0011000F2Q000B012Q00017Q00013Q0003083Q00667073422Q6F737401084Q004D00015Q0020E300010001000100069A2Q01000700013Q00040F012Q000700012Q004D000100014Q004601026Q00330001000200012Q000B012Q00017Q00103Q00028Q0003063Q0069706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E7473026Q00F03F025Q00C0924003043Q007461736B03043Q007761697403063Q006670734D61782Q033Q0049734103053Q00446563616C03073Q005465787475726503053Q007063612Q6C03083Q00426173655061727403093Q00436861726163746572030E3Q00497344657363656E64616E744F66003B3Q0012593Q00013Q00122Q000100023Q00122Q000200033Q00202Q0002000200044Q000200036Q00013Q000300044Q003800010020AC014Q00050020F600063Q00060026810106000E0001000100040F012Q000E0001001288010600073Q0020E30006000600082Q00610106000100012Q004D00066Q00F9000700056Q0006000200014Q000600013Q00202Q00060006000900062Q0006003700013Q00040F012Q0037000100208D00060005000A0012160008000B4Q00FC0006000800020006570106001F0001000100040F012Q001F000100208D00060005000A0012160008000C4Q00FC00060008000200069A0106002400013Q00040F012Q002400010012880106000D3Q0006B700073Q000100012Q0046012Q00054Q003300060002000100040F012Q0037000100208D00060005000A0012160008000E4Q00FC00060008000200069A0106003700013Q00040F012Q003700012Q004D000600023Q0020E300060006000F00069A0106003300013Q00040F012Q0033000100208D0006000500102Q004D000800023Q0020E300080008000F2Q00FC000600080002000657010600370001000100040F012Q003700010012880106000D3Q0006B700070001000100012Q0046012Q00054Q00330006000200012Q000F00045Q00062B000100070001000200040F012Q000700012Q000B012Q00013Q00023Q00023Q00030C3Q005472616E73706172656E6379026Q00F03F00034Q004D7Q0030933Q000100022Q000B012Q00017Q00073Q0003083Q004D6174657269616C03043Q00456E756D030D3Q00536D2Q6F7468506C6173746963030B3Q005265666C656374616E6365028Q00030A3Q0043617374536861646F77012Q000A4Q004D7Q0012882Q0100023Q0020E30001000100010020E300010001000300105D012Q000100012Q004D7Q0030933Q000400052Q004D7Q0030933Q000600072Q000B012Q00017Q00033Q0003053Q007063612Q6C03023Q00686C0001124Q004D00016Q0073000100013Q00069A2Q01001100013Q00040F012Q00110001001288010200013Q0006B700033Q000100012Q0046012Q00014Q00330002000200010020E300020001000200069A0102000F00013Q00040F012Q000F0001001288010200013Q0006B700030001000100012Q0046012Q00014Q00330002000200012Q004D00025Q00202C00023Q00032Q000B012Q00013Q00023Q00023Q0003023Q002Q6203073Q0044657374726F7900054Q005A7Q00206Q000100206Q00026Q000200016Q00017Q00023Q0003023Q00686C03073Q0044657374726F7900054Q005A7Q00206Q000100206Q00026Q000200016Q00017Q00243Q0003023Q002Q6203063Q00506172656E74030C3Q0042692Q6C626F61726447756903043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574025Q00406540026Q004340030B3Q00416C776179734F6E546F702Q01030B3Q0053747564734F2Q6673657403073Q00566563746F72332Q033Q006E6577028Q00026Q00084003073Q0041646F726E2Q6503093Q00546578744C6162656C026Q00F03F03163Q004261636B67726F756E645472616E73706172656E6379030A3Q0054657874436F6C6F723303043Q00466F6E7403043Q00456E756D030A3Q00476F7468616D426F6C6403083Q005465787453697A65026Q002A4003163Q00546578745374726F6B655472616E73706172656E6379029A5Q99D93F030A3Q006573704F75746C696E6503093Q00486967686C6967687403103Q0046692Q6C5472616E73706172656E6379030C3Q004F75746C696E65436F6C6F7203093Q0044657074684D6F646503123Q00486967686C6967687444657074684D6F64652Q033Q006C626C03023Q00686C03043Q005465787405544Q004D00056Q0073000500053Q00069A0105000800013Q00040F012Q000800010020E30006000500010020E30006000600020006570106004F0001000100040F012Q004F00012Q004D000600014Q007500078Q0006000200014Q000600023Q00122Q000700036Q00083Q000400122Q000900053Q00202Q00090009000600122Q000A00073Q00122Q000B00086Q0009000B000200105D01080004000900309300080009000A0012880109000C3Q0020E300090009000D001216000A000E3Q001216000B000F3Q001216000C000E4Q00FC0009000C000200105D0108000B000900105D0108001000012Q004D000900034Q00FC0006000900022Q004D000700023Q00121E000800116Q00093Q000600122Q000A00053Q00202Q000A000A000D00122Q000B00123Q00122Q000C000E3Q00122Q000D00123Q00122Q000E000E6Q000A000E000200102Q00090004000A00309300090013001200105D010900140003001288010A00163Q0020E3000A000A00150020E3000A000A001700105D01090015000A0030930009001800190030930009001A001B2Q0046010A00064Q00FC0007000A00022Q0062000800084Q004D000900043Q0020E300090009001C00069A0109004800013Q00040F012Q0048000100069A0102004800013Q00040F012Q004800012Q004D000900023Q001253010A001D6Q000B3Q000400102Q000B0010000200302Q000B001E001200102Q000B001F000300122Q000C00163Q00202Q000C000C002100202Q000C000C000900102Q000B0020000C4Q000C00036Q0009000C00024Q000800094Q001301093Q000300105D01090001000600105D01090022000700105D0109002300082Q0046010500094Q004D00096Q009E00093Q00050020E300060005002200105D0106002400040020E300060005000100105D0106001000012Q000B012Q00017Q00013Q0003053Q007063612Q6C00094Q0013016Q0012882Q0100013Q0006B700023Q000100032Q004D8Q004D3Q00014Q0046017Q00330001000200012Q00DA3Q00024Q000B012Q00013Q00013Q000D3Q0003063Q0069706169727303093Q0047657454612Q67656403093Q0042652Q72794275736803053Q007461626C6503063Q00696E736572742Q033Q006F626A03043Q007061727403043Q006E616D6503083Q00746F737472696E67030C3Q00476574412Q7472696275746503093Q0042652Q72794E616D6503053Q0042652Q727903043Q004E616D6500243Q001288012Q00014Q004D00015Q00208D000100010002001216000300034Q00A12Q0100034Q0035014Q000200040F012Q002100012Q004D000500014Q0046010600044Q009C01050002000200069A0105002100013Q00040F012Q00210001001288010600043Q0020E30006000600052Q004D000700024Q001301083Q000300105D01080006000400105D010800070005001288010900093Q00208D000A0004000A001216000C000B4Q00FC000A000C0002000657010A001E0001000100040F012Q001E000100208D000A0004000A001216000C000C4Q00FC000A000C0002000657010A001E0001000100040F012Q001E00010020E3000A0004000D2Q009C01090002000200105D0108000800092Q00EE00060008000100062B3Q00070001000200040F012Q000700012Q000B012Q00017Q001D3Q00030A3Q00657370506C617965727303063Q00697061697273030A3Q00476574506C617965727303093Q00436861726163746572030E3Q0046696E6446697273744368696C6403103Q0048756D616E6F6964522Q6F74506172742Q0103063Q00436F6C6F723303073Q0066726F6D524742025Q00E06F40026Q00544003043Q004E616D6503093Q006573704672756974732Q033Q006F626A03043Q0070617274025Q00C06740026Q004E4003043Q006E616D6503093Q00657370436865737473025Q00806B40030A3Q0065737042652Q72696573026Q005E40026Q00694003073Q0042652Q72793A2003093Q0065737049736C616E64030B3Q004765744368696C6472656E025Q00C06240025Q0040654003053Q00706169727300B94Q0013017Q004D00016Q00652Q01000100020006B700023Q000100022Q004D3Q00014Q0046012Q00014Q004D000300013Q0020E300030003000100069A0103002F00013Q00040F012Q002F0001001288010300024Q004D000400023Q00208D0004000400032Q00DE000400054Q003501033Q000500040F012Q002D00012Q004D000800033Q0006AD0007002D0001000800040F012Q002D00010020E300080007000400069A0108002D00013Q00040F012Q002D00010020E300080007000400208D000800080005001216000A00064Q00FC0008000A000200069A0108002D00013Q00040F012Q002D000100202C3Q000700072Q00BA000900046Q000A00076Q000B00083Q00202Q000C0007000400122Q000D00083Q00202Q000D000D000900122Q000E000A3Q00122Q000F000B3Q00122Q0010000B6Q000D0010000200202Q000E0007000C4Q000F00026Q001000086Q000F000200024Q000E000E000F4Q0009000E000100062B000300100001000200040F012Q001000012Q004D000300013Q0020E300030003000D00069A0103004C00013Q00040F012Q004C0001001288010300024Q004D000400054Q0077010400014Q003501033Q000500040F012Q004A00010020E300080007000E00202C3Q000800072Q004D000800043Q0020E300090007000E0020E3000A0007000F0020E3000B0007000E001288010C00083Q0020E3000C000C0009001216000D000A3Q001216000E00103Q001216000F00114Q00FC000C000F00020020A8000D000700124Q000E00023Q00202Q000F0007000F4Q000E000200024Q000D000D000E4Q0008000D000100062B000300380001000200040F012Q003800012Q004D000300013Q0020E300030003001300069A0103006900013Q00040F012Q00690001001288010300024Q004D000400064Q0077010400014Q003501033Q000500040F012Q006700010020E300080007000E00202C3Q000800072Q004D000800043Q0020E300090007000E0020E3000A0007000F2Q0062000B000B3Q001288010C00083Q0020E3000C000C0009001216000D000B3Q001216000E00143Q001216000F000A4Q00FC000C000F00020020A8000D000700124Q000E00023Q00202Q000F0007000F4Q000E000200024Q000D000D000E4Q0008000D000100062B000300550001000200040F012Q005500012Q004D000300013Q0020E300030003001500069A0103008700013Q00040F012Q00870001001288010300024Q004D000400074Q0077010400014Q003501033Q000500040F012Q008500010020E300080007000E00202C3Q000800072Q004D000800043Q0020E300090007000E0020E3000A0007000F2Q0062000B000B3Q001288010C00083Q0020E3000C000C0009001216000D000A3Q001216000E00163Q001216000F00174Q00FC000C000F0002001216000D00183Q0020A8000E000700124Q000F00023Q00202Q00100007000F4Q000F000200024Q000D000D000F4Q0008000D000100062B000300720001000200040F012Q007200012Q004D000300013Q0020E300030003001900069A010300AC00013Q00040F012Q00AC00012Q004D000300084Q006501030001000200069A010300AC00013Q00040F012Q00AC0001001288010400023Q00208D00050003001A2Q00DE000500064Q003501043Q000600040F012Q00AA00012Q004D000900094Q0046010A00084Q009C01090002000200069A010900AA00013Q00040F012Q00AA000100202C3Q000800072Q005C010A00046Q000B00086Q000C00096Q000D000D3Q00122Q000E00083Q00202Q000E000E000900122Q000F001B3Q00122Q0010000A3Q00122Q0011001C6Q000E001100020020E3000F0008000C2Q0046011000024Q0046011100094Q009C0110000200022Q0087000F000F00102Q00EE000A000F000100062B000400940001000200040F012Q009400010012880103001D4Q004D0004000A4Q00B200030002000500040F012Q00B600012Q007300073Q0006000657010700B60001000100040F012Q00B600012Q004D0007000B4Q0046010800064Q003300070002000100062B000300B00001000100040F012Q00B000012Q000B012Q00013Q00013Q00083Q0003073Q006573704469737403023Q000A5B03043Q006D61746803053Q00666C2Q6F7203083Q00506F736974696F6E03093Q004D61676E697475646503023Q006D5D034Q0001164Q004D00015Q0020E300010001000100069A2Q01001300013Q00040F012Q001300012Q004D000100013Q00069A2Q01001300013Q00040F012Q00130001001216000100023Q00122E010200033Q00202Q00020002000400202Q00033Q00054Q000400013Q00202Q0004000400054Q00030003000400202Q0003000300064Q00020002000200122Q000300076Q0001000100032Q00DA000100023Q001216000100084Q00DA000100024Q000B012Q00017Q00013Q0003053Q007061697273000A3Q001288012Q00014Q004D00016Q00B23Q0002000200040F012Q000700012Q004D000400014Q0046010500034Q003300040002000100062B3Q00040001000100040F012Q000400012Q000B012Q00017Q00093Q00029A5Q99D93F028Q00030A3Q00657370506C617965727303093Q0065737046727569747303093Q00657370436865737473030A3Q0065737042652Q7269657303093Q0065737049736C616E6403053Q007063612Q6C03043Q006E65787401294Q009F00018Q000100016Q00018Q00015Q00262Q000100070001000100040F012Q000700012Q000B012Q00013Q001216000100024Q00B800016Q004D000100013Q0020E30001000100030006572Q01001D0001000100040F012Q001D00012Q004D000100013Q0020E30001000100040006572Q01001D0001000100040F012Q001D00012Q004D000100013Q0020E30001000100050006572Q01001D0001000100040F012Q001D00012Q004D000100013Q0020E30001000100060006572Q01001D0001000100040F012Q001D00012Q004D000100013Q0020E300010001000700069A2Q01002100013Q00040F012Q002100010012882Q0100084Q004D000200024Q003300010002000100040F012Q002800010012882Q0100094Q004D000200034Q009C2Q010002000200069A2Q01002800013Q00040F012Q002800012Q004D000100044Q00612Q01000100012Q000B012Q00017Q000A3Q00030A3Q0073616265725374616765030B3Q007361626572506C6174657303093Q0073616265724275726E026Q00F03F010003073Q006C617374476574028Q0003043Q0073746570034Q0003053Q00737461676500104Q001A9Q0000018Q00025Q00122Q000300046Q00045Q00302Q00020003000500102Q00010002000400104Q000100038Q000300304Q0006000700304Q0008000900304Q000A00046Q00018Q00028Q000100016Q00017Q000A3Q0003063Q00506172656E7403043Q0054657874030A3Q0053756120726163613A20030E3Q002Q207C2Q2056657273616F3A2056027Q0040030B3Q00202865766F6C7569646129034Q0003043Q007461736B03043Q0077616974026Q000840001C4Q004D7Q000657012Q001B0001000100040F012Q001B00012Q004D3Q00013Q0020E35Q000100069A012Q001B00013Q00040F012Q001B00012Q004D3Q00024Q00B13Q000100012Q004D000200033Q001216000300034Q004601045Q001216000500044Q0046010600013Q000EF3000500130001000100040F012Q00130001001216000700063Q000657010700140001000100040F012Q00140001001216000700074Q008700030003000700101500020002000300122Q000200083Q00202Q00020002000900122Q0003000A6Q00020002000100046Q00012Q000B012Q00017Q00023Q0003043Q005465787403083Q005374617475733A2001064Q004D00015Q001216000200024Q004601036Q008700020002000300105D2Q01000100022Q000B012Q00019Q003Q00054Q004D7Q0006B700013Q000100012Q004D3Q00014Q00333Q000200012Q000B012Q00013Q00013Q00013Q0003053Q00667275697401054Q00C100015Q00122Q000200016Q00038Q0001000300016Q00019Q003Q00054Q0085019Q002Q000100016Q00018Q000100016Q00017Q00113Q0003063Q00697061697273030B3Q004765744368696C6472656E03063Q00737472696E6703053Q006D6174636803043Q004E616D65030A3Q005E49736C616E6420256403053Q007461626C6503063Q00696E7365727403043Q00736F7274030A3Q007365744F7074696F6E7303043Q0054657874028Q0003293Q004E616F20656E636F6E747265692061206C6973746120646520696C686173206465737465206D61722E03043Q00536561202Q033Q004D617203023Q003A2003073Q0020696C6861732E00384Q004D8Q0061012Q000100012Q0013017Q004D000100014Q00652Q010001000200069A2Q01001A00013Q00040F012Q001A0001001288010200013Q00208D0003000100022Q00DE000300044Q003501023Q000400040F012Q00180001001288010700033Q0020E30007000700040020E3000800060005001216000900064Q00FC000700090002000657010700180001000100040F012Q00180001001288010700073Q0020E30007000700082Q004601085Q0020E30009000600052Q00EE00070009000100062B0002000C0001000200040F012Q000C0001001288010200073Q0020E30002000200092Q004601036Q00330002000200012Q004D000200023Q0020E300020002000A2Q004601036Q00330002000200012Q004D000200034Q00D000035Q002681010300290001000C00040F012Q002900010012160003000D3Q000657010300360001000100040F012Q003600012Q004D000300043Q000ED3000C00310001000300040F012Q003100010012160003000E4Q004D000400044Q0087000300030004000657010300320001000100040F012Q003200010012160003000F3Q001216000400104Q00D000055Q001216000600114Q008700030003000600105D0102000B00032Q000B012Q00017Q00033Q00026Q00F03F03043Q007461736B03053Q00737061776E01194Q004D00015Q0020AC2Q01000100012Q00B800016Q004D00015Q000657012Q00090001000100040F012Q000900012Q00E700026Q00B8000200014Q000B012Q00013Q001288010200023Q0020E30002000200030006B700033Q0001000B2Q004D8Q0046012Q00014Q004D3Q00024Q004D3Q00034Q004D3Q00014Q004D3Q00044Q004D3Q00054Q004D3Q00064Q004D3Q00074Q004D3Q00084Q004D3Q00094Q00330002000200012Q000B012Q00013Q00013Q00143Q0003063Q0069736C616E64034Q0003043Q0054657874031A3Q004573636F6C686120756D6120696C6861207072696D6569726F2E03353Q00496E646F20706172612061205375626D65726765642049736C616E642070656C6F205375626D6172696E6520576F726B65723Q2E031E3Q00566F63652065737461206E61205375626D65726765642049736C616E642E030E3Q0046696E6446697273744368696C6403053Q007063612Q6C030A3Q00496E646F2070617261202Q033Q003Q2E03063Q00434672616D652Q033Q006E657703073Q00566563746F7233028Q00025Q0080514003073Q00747053702Q6564030A3Q00436865676F7520656D2003133Q0054656C65706F7274652063616E63656C61646F03263Q004E616F20636F6E7365677569206C6572206120706F736963616F2064652Q736120696C68612E03043Q007470476F00593Q0006B75Q000100032Q004D8Q004D3Q00014Q004D3Q00024Q00B6000100033Q00202Q0001000100014Q000200016Q000200043Q00262Q0001000D0001000200040F012Q000D00012Q004D000200053Q00309300020003000400040F012Q004E00012Q004D000200064Q0046010300014Q009C01020002000200069A0102001E00013Q00040F012Q001E00012Q004D000200053Q0030930002000300052Q004D000200074Q004601035Q0006B700040001000100012Q004D3Q00054Q00FC00020004000200069A0102004E00013Q00040F012Q004E00012Q004D000300053Q00309300030003000600040F012Q004E00012Q004D000200084Q0065010200010002000621000300250001000200040F012Q0025000100208D0003000200072Q0046010500014Q00FC000300050002001288010400083Q0006B700050002000100012Q0046012Q00034Q00B200040002000500069A0104004B00013Q00040F012Q004B00012Q004D000600053Q001216000700094Q0046010800013Q0012160009000A4Q008700070007000900105D0106000300072Q004D000600093Q0012880107000B3Q0020E300070007000C0012030008000D3Q00202Q00080008000C00122Q0009000E3Q00122Q000A000F3Q00122Q000B000E6Q0008000B00024Q0008000500084Q0007000200024Q000800033Q00202Q0008000800102Q004601096Q00FC0006000900022Q004D000700053Q00069A0106004800013Q00040F012Q00480001001216000800114Q0046010900014Q0087000800080009000657010800490001000100040F012Q00490001001216000800123Q00105D01070003000800040F012Q004D00012Q004D000600053Q0030930006000300132Q000F00026Q00E700026Q00B8000200044Q004D00026Q004D000300013Q000627000200580001000300040F012Q005800012Q004D0002000A3Q001216000300144Q00E700046Q00EE0002000400012Q000B012Q00013Q00038Q000B4Q004D8Q004D000100013Q0006273Q00070001000100040F012Q000700012Q004D3Q00024Q00A77Q00040F012Q000900012Q0011017Q00E73Q00014Q00DA3Q00024Q000B012Q00017Q00013Q0003043Q005465787401034Q004D00015Q00105D2Q0100014Q000B012Q00017Q00023Q0003083Q004765745069766F7403083Q00506F736974696F6E00064Q00CD7Q00206Q00016Q0002000200206Q00026Q00028Q00017Q00033Q0003043Q0054657874030E3Q005669616A616E646F2070617261202Q033Q003Q2E020A4Q005801025Q00122Q000300026Q000400013Q00122Q000500036Q00030003000500102Q0002000100034Q000200016Q00038Q0002000200016Q00017Q00023Q00030A3Q0054726176656C4D61696E03053Q00536561203100054Q004D7Q001216000100013Q001216000200024Q00EE3Q000200012Q000B012Q00017Q00023Q00030F3Q0054726176656C4472652Q73726F736103053Q00536561203200054Q004D7Q001216000100013Q001216000200024Q00EE3Q000200012Q000B012Q00017Q00023Q0003093Q0054726176656C5A6F7503053Q00536561203300054Q004D7Q001216000100013Q001216000200024Q00EE3Q000200012Q000B012Q00019Q003Q00034Q004D8Q0061012Q000100012Q000B012Q00017Q00023Q0003093Q0057616C6B53702Q6564026Q00304001083Q000657012Q00070001000100040F012Q000700012Q004D00016Q00652Q010001000200069A2Q01000700013Q00040F012Q000700010030930001000100022Q000B012Q00017Q000B3Q0003053Q007370644F6E2Q033Q0063666D030D3Q004D6F7665446972656374696F6E03093Q004D61676E6974756465028Q0003063Q00434672616D6503043Q006D6174682Q033Q006D617803083Q0073702Q656456616C026Q00304003093Q0057616C6B53702Q656401284Q004D00015Q0020E30001000100010006572Q0100050001000100040F012Q000500012Q000B012Q00014Q004D000100014Q00652Q01000100020006572Q01000A0001000100040F012Q000A00012Q000B012Q00014Q004D00025Q0020E300020002000200069A0102002400013Q00040F012Q002400012Q004D000200024Q006501020001000200069A0102002700013Q00040F012Q002700010020E30003000100030020E3000300030004000ED3000500270001000300040F012Q002700010020E30003000200060020E3000400010003001288010500073Q0020E30005000500082Q004D00065Q0020E300060006000900207800060006000A001216000700054Q00FC0005000700022Q00600004000400052Q0060000400044Q003301030003000400105D01020006000300040F012Q002700012Q004D00025Q0020E300020002000900105D2Q01000B00022Q000B012Q00017Q00053Q0003043Q00696E666A030B3Q004368616E6765537461746503043Q00456E756D03113Q0048756D616E6F696453746174655479706503073Q004A756D70696E67000E4Q004D7Q0020E35Q000100069A012Q000D00013Q00040F012Q000D00012Q004D3Q00014Q0065012Q0001000200069A012Q000D00013Q00040F012Q000D000100208D00013Q0002001288010300033Q0020E30003000300040020E30003000300052Q00EE0001000300012Q000B012Q00017Q00023Q0003043Q005465787403163Q004175746F205374617475733A206465736C696761646F01053Q000657012Q00040001000100040F012Q000400012Q004D00015Q0030930001000100022Q000B012Q00017Q00293Q002Q033Q006B657903093Q00737461744D656C2Q6503043Q006E616D6503053Q004D656C2Q65030B3Q0073746174446566656E736503073Q00446566656E736503093Q007374617453776F726403053Q0053776F726403073Q007374617447756E2Q033Q0047756E03093Q00737461744672756974030B3Q0044656D6F6E20467275697403063Q00506172656E7403093Q006175746F537461747303063Q0069706169727303053Q007461626C6503063Q00696E73657274028Q0003053Q007063612Q6C03043Q005465787403393Q004175746F205374617475733A206D61727175652070656C6F206D656E6F7320756D2073746174757320656D2053656C6563742053746174757303233Q004175746F205374617475733A2073656D20706F6E746F7320646973706F6E697665697303043Q006D6174682Q033Q006D6178026Q00F03F03053Q00666C2Q6F7203073Q00737461745065722Q033Q006D696E03083Q00412Q64506F696E7403023Q00202B03083Q00737461744C656674030A3Q004175746F6D617469636F035Q0003083Q002028736F62726129030D3Q004175746F205374617475733A2003063Q00636F6E6361742Q033Q00207C2003043Q007461736B03043Q0077616974026Q00F83F00A44Q0013012Q00054Q00132Q013Q00020030930001000100020030930001000300042Q001301023Q00020030930002000100050030930002000300062Q001301033Q00020030930003000100070030930003000300082Q001301043Q000200306B01040001000900302Q00040003000A4Q00053Q000200302Q00050001000B00302Q00050003000C6Q000500010006B700013Q000100012Q004D8Q004D000200013Q000657010200A30001000100040F012Q00A300012Q004D000200023Q0020E300020002000D00069A010200A300013Q00040F012Q00A300012Q004D000200033Q0020E300020002000E00069A0102009E00013Q00040F012Q009E00012Q001301025Q0012880103000F4Q004601046Q00B200030002000500040F012Q002D00012Q004D000800033Q0020E30009000700012Q007300080008000900069A0108002D00013Q00040F012Q002D0001001288010800103Q0020E30008000800112Q0046010900023Q0020E3000A000700032Q00EE0008000A000100062B000300230001000200040F012Q00230001001216000300123Q001288010400133Q0006B700050001000100022Q0046012Q00034Q004D8Q00330004000200012Q00D0000400023Q0026810104003B0001001200040F012Q003B00012Q004D000400043Q00309300040014001500040F012Q009D00010026AB000300400001001200040F012Q004000012Q004D000400043Q00309300040014001600040F012Q009D00012Q0046010400033Q001288010500173Q0020E3000500050018001216000600193Q001288010700173Q0020E300070007001A2Q004D000800033Q0020E300080008001B2Q00DE000700084Q000400053Q00022Q004100065Q00122Q0007000F6Q000800026Q00070002000900044Q00640001001288010C00173Q0020E3000C000C001C2Q0046010D00054Q0046010E00044Q00FC000C000E0002000ED3001200640001000C00040F012Q006400012Q004D000D00053Q001265000E001D6Q000F000B6Q0010000C6Q000D001000014Q00040004000C00122Q000D00103Q00202Q000D000D00114Q000E00066Q000F000B3Q00122Q0010001E6Q0011000C6Q000F000F00114Q000D000F000100062B0007004F0001000200040F012Q004F0001000ED3001200940001000400040F012Q009400012Q004D000700033Q0020E300070007001F00267B000700700001002000040F012Q0070000100267B000700700001002100040F012Q00700001002681010700860001002200040F012Q008600010020E30007000200192Q0046010800013Q0020E30009000200192Q009C0108000200020012880109000F4Q0046010A00024Q00B200090002000B00040F012Q008400012Q0046010E00014Q0046010F000D4Q009C010E0002000200069A010E008400013Q00040F012Q0084000100069A0108008100013Q00040F012Q00810001000676010E00840001000800040F012Q008400012Q0046010F000D4Q00460108000E4Q00460107000F3Q00062B000900780001000200040F012Q007800012Q004D000800053Q00122Q0009001D6Q000A00076Q000B00046Q0008000B000100122Q000800103Q00202Q0008000800114Q000900066Q000A00073Q00122Q000B001E6Q000C00043Q001216000D00234Q0087000A000A000D2Q00EE0008000A00012Q004D000700043Q001216000800243Q001288010900103Q0020E30009000900252Q0046010A00063Q001216000B00264Q00FC0009000B00022Q008700080008000900105D0107001400082Q000F00025Q001288010200273Q0020E3000200020028001216000300294Q003300020002000100040F012Q001300012Q000B012Q00013Q00023Q00023Q0003053Q007063612Q6C03083Q00746F6E756D626572010F3Q0012882Q0100013Q0006B700023Q000100022Q004D8Q0046017Q00B200010002000200069A2Q01000C00013Q00040F012Q000C0001001288010300024Q0046010400024Q009C0103000200020006570103000D0001000100040F012Q000D00012Q0062000300034Q00DA000300024Q000B012Q00013Q00013Q00043Q0003043Q004461746103053Q00537461747303053Q004C6576656C03053Q0056616C756500094Q006E016Q00206Q000100206Q00024Q000100019Q00000100206Q000300206Q00046Q00028Q00017Q00053Q0003083Q00746F6E756D62657203043Q004461746103063Q00506F696E747303053Q0056616C7565029Q000B3Q0012373Q00016Q000100013Q00202Q00010001000200202Q00010001000300202Q0001000100046Q0002000200064Q00090001000100040F012Q000900010012163Q00054Q00B88Q000B012Q00019Q002Q0001053Q00069A012Q000400013Q00040F012Q000400012Q004D00016Q00612Q01000100012Q000B012Q00017Q00023Q0003043Q007461736B03053Q00737061776E00104Q004D7Q00069A012Q000400013Q00040F012Q000400012Q000B012Q00014Q00E73Q00014Q00B87Q001288012Q00013Q0020E35Q00020006B700013Q000100052Q004D3Q00014Q004D3Q00024Q004D8Q004D3Q00034Q004D3Q00044Q00333Q000200012Q000B012Q00013Q00013Q001D3Q00030E3Q0046696E6446697273744368696C6403073Q0052656D6F74657303063Q005265642Q656D03043Q005465787403203Q0052656D6F746520646520636F6469676F73206E616F20656E636F6E747261646F028Q0003063Q00697061697273030B3Q00526573676174616E646F2003013Q002F03023Q003A2003053Q007063612Q6C03063Q00737472696E6703053Q006C6F77657203083Q00746F737472696E6700010003043Q0066696E6403073Q00696E76616C6964026Q00F03F03073Q006578706972656403073Q00616C726561647903043Q007573656403043Q006E6F742003043Q007461736B03043Q0077616974026Q33E33F03083Q0050726F6E746F3A20030C3Q002061636569746F2873292C2003223Q0020726563757361646F2873292028757361646F73206F7520657870697261646F732900774Q00F87Q00206Q000100122Q000200028Q0002000200062Q0001000900013Q00040F012Q0009000100208D00013Q0001001216000300034Q00FC0001000300020006572Q0100100001000100040F012Q001000012Q004D000200013Q0030930002000400052Q00E700026Q00B8000200024Q000B012Q00013Q001216000200063Q001216000300063Q001288010400074Q004D000500034Q00B200040002000600040F012Q006A00012Q004D000900043Q00069A0109001A00013Q00040F012Q001A000100040F012Q006C00012Q004D000900013Q001216000A00084Q0046010B00073Q001216000C00094Q004D000D00034Q00D0000D000D3Q001216000E000A4Q0046010F00084Q0087000A000A000F00105D01090004000A0012880109000B3Q0006B7000A3Q000100022Q0046012Q00014Q0046012Q00084Q006900090002000A00122Q000B000C3Q00202Q000B000B000D00122Q000C000E6Q000D000A6Q000C000D6Q000B3Q000200062Q0009006200013Q00040F012Q0062000100267B000A00620001000F00040F012Q0062000100267B000A00620001001000040F012Q00620001001288010C000C3Q00207C000C000C00114Q000D000B3Q00122Q000E00123Q00122Q000F00136Q001000016Q000C0010000200062Q000C00620001000100040F012Q00620001001288010C000C3Q00207C000C000C00114Q000D000B3Q00122Q000E00143Q00122Q000F00136Q001000016Q000C0010000200062Q000C00620001000100040F012Q00620001001288010C000C3Q00207C000C000C00114Q000D000B3Q00122Q000E00153Q00122Q000F00136Q001000016Q000C0010000200062Q000C00620001000100040F012Q00620001001288010C000C3Q00207C000C000C00114Q000D000B3Q00122Q000E00163Q00122Q000F00136Q001000016Q000C0010000200062Q000C00620001000100040F012Q00620001001288010C000C3Q0020A6000C000C00114Q000D000B3Q00122Q000E00173Q00122Q000F00136Q001000016Q000C0010000200062Q000C006400013Q00040F012Q006400010020AC01030003001300040F012Q006500010020AC010200020013001288010C00183Q0020E3000C000C0019001216000D001A4Q0033000C000200012Q000F00075Q00062B000400160001000200040F012Q001600012Q004D000400013Q0012490005001B6Q000600023Q00122Q0007001C6Q000800033Q00122Q0009001D6Q00050005000900102Q0004000400054Q00048Q000400028Q00013Q00013Q00013Q00030C3Q00496E766F6B6553657276657200064Q00B07Q00206Q00014Q000200018Q00029Q008Q00017Q00023Q0003103Q006964656E746966796578656375746F7203083Q00746F737472696E6700093Q001288012Q00013Q00069A012Q000800013Q00040F012Q00080001001288012Q00023Q0012882Q0100014Q00772Q0100014Q00045Q00022Q00B88Q000B012Q00017Q000B3Q0003063Q00506172656E7403043Q0054657874030E3Q00426C6F7820467275697420C2B72003043Q0020C2B720028Q0003043Q005365612003053Q00536561203F03073Q0020C2B7204C762003043Q007461736B03043Q0077616974027Q004000234Q004D7Q000657012Q00220001000100040F012Q002200012Q004D3Q00013Q0020E35Q000100069A012Q002200013Q00040F012Q002200012Q004D3Q00024Q0027012Q000100016Q00033Q00122Q000100036Q000200043Q00122Q000300046Q000400053Q000E2Q000500150001000400040F012Q00150001001216000400064Q004D000500054Q0087000400040005000657010400160001000100040F012Q00160001001216000400073Q001216000500084Q0070000600066Q00060001000200122Q000700046Q000800076Q00010001000800104Q0002000100124Q00093Q00206Q000A00122Q0001000B8Q0002000100046Q00012Q000B012Q00017Q00073Q0003073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503043Q005465787403313Q0043612Q72656761646F2120557365206F20626F74616F207265646F6E646F20706172612061627269722F6665636861722E03083Q004475726174696F6E026Q001440000A4Q004D7Q00208D5Q0001001216000200024Q001301033Q00032Q004D000400013Q00105D0103000300040030930003000400050030930003000600072Q00EE3Q000300012Q000B012Q00017Q00", GetFEnv(), ...);
