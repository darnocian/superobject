(*
  *                         Super Object Toolkit
  *
  * Usage allowed under the restrictions of the Lesser GNU General Public License
  * or alternatively the restrictions of the Mozilla Public License 1.1
  *
  * Software distributed under the License is distributed on an "AS IS" basis,
  * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License for
  * the specific language governing rights and limitations under the License.
  *
  * Embarcadero Technologies Inc is not permitted to use or redistribute
  * this source code without explicit permission.
  *
  * Unit owner : Henri Gourvest <hgourvest@gmail.com>
  * Web site   : http://www.progdigy.com
  *
  * This unit is inspired from the json c lib:
  *   Michael Clark <michael@metaparadigm.com>
  *   http://oss.metaparadigm.com/json-c/
  *
  *  CHANGES:
  *  v1.2
  *   + support of currency data type
  *   + right trim unquoted string
  *   + read Unicode Files and streams (Litle Endian with BOM)
  *   + Fix bug on javadate functions + windows nt compatibility
  *   + Now you can force to parse only the canonical syntax of JSON using the stric parameter
  *   + Delphi 2010 RTTI marshalling
  *  v1.1
  *   + Double licence MPL or LGPL.
  *   + Delphi 2009 compatibility & Unicode support.
  *   + AsString return a string instead of PChar.
  *   + Escaped and Unascaped JSON serialiser.
  *   + Missed FormFeed added \f
  *   - Removed @ trick, uses forcepath() method instead.
  *   + Fixed parse error with uppercase E symbol in numbers.
  *   + Fixed possible buffer overflow when enlarging array.
  *   + Added "delete", "pack", "insert" methods for arrays and/or objects
  *   + Multi parametters when calling methods
  *   + Delphi Enumerator (for obj1 in obj2 do ...)
  *   + Format method ex: obj.format('<%name%>%tab[1]%</%name%>')
  *   + ParseFile and ParseStream methods
  *   + Parser now understand hexdecimal c syntax ex: \xFF
  *   + Null Object Design Patern (ex: for obj in values.N['path'] do ...)
  *  v1.0
  *   + renamed class
  *   + interfaced object
  *   + added a new data type: the method
  *   + parser can now evaluate properties and call methods
  *   - removed obselet rpc class
  *   - removed "find" method, now you can use "parse" method instead
  *  v0.6
  *   + refactoring
  *  v0.5
  *   + new find method to get or set value using a path syntax
  *       ex: obj.s['obj.prop[1]'] := 'string value';
  *           obj.a['@obj.array'].b[n] := true; // @ -> create property if necessary
  *  v0.4
  *   + bug corrected: AVL tree badly balanced.
  *  v0.3
  *   + New validator partially based on the Kwalify syntax.
  *   + extended syntax to parse unquoted fields.
  *   + Freepascal compatibility win32/64 Linux32/64.
  *   + JavaToDelphiDateTime and DelphiToJavaDateTime improved for UTC.
  *   + new TJsonObject.Compare function.
  *  v0.2
  *   + Hashed string list replaced with a faster AVL tree
  *   + JsonInt data type can be changed to int64
  *   + JavaToDelphiDateTime and DelphiToJavaDateTime helper fonctions
  *   + from json-c v0.7
  *     + Add escaping of backslash to json output
  *     + Add escaping of foward slash on tokenizing and output
  *     + Changes to internal tokenizer from using recursion to
  *       using a depth state structure to allow incremental parsing
  *  v0.1
  *   + first release
*)

{$IFDEF FPC}
{$MODE OBJFPC}{$H+}
{$ENDIF}
{$DEFINE SUPER_METHOD}
{ .$DEFINE DEBUG } // track memory leack

{$IF defined(DCC) and (CompilerVersion >= 2.1)}
{$DEFINE VER210ORGREATER}
{$ENDIF}
{$IF defined(DCC) and (CompilerVersion >= 2.3)}
{$DEFINE VER230ORGREATER}
{$ENDIF}
{$IF defined(FPC)}
{$DEFINE HAVE_INLINE}
{$ENDIF}
{$IF defined(DCC) and (CompilerVersion >= 1.7)}
{$DEFINE HAVE_INLINE}
{$ENDIF}
{$IF defined(VER210ORGREATER)}
{$DEFINE HAVE_RTTI}
{$ENDIF}
{$IF defined(VER230ORGREATER)}
{$DEFINE NEED_FORMATSETTINGS}
{$ENDIF}
{$IF defined(FPC) and defined(VER2_6)}
{$DEFINE NEED_FORMATSETTINGS}
{$ENDIF}
{$OVERFLOWCHECKS OFF}
{$RANGECHECKS OFF}
unit superobject;

interface

uses
  Classes, supertypes
{$IFDEF HAVE_RTTI}
    , Generics.Collections, RTTI, TypInfo
{$ENDIF}
    ;

const
  SUPER_ARRAY_LIST_DEFAULT_SIZE = 32;
  SUPER_TOKENER_MAX_DEPTH = 32;

  SUPER_AVL_MAX_DEPTH = sizeof(LongInt) * 8;
  SUPER_AVL_MASK_HIGH_BIT = not((not longword(0)) shr 1);

type

  // forward declarations
  TSuperObject = class;
  ISuperObject = interface;
  TSuperArray = class;

  (* AVL Tree
    *  This is a "special" autobalanced AVL tree
    *  It use a hash value for fast compare
  *)

  IGenericClassName = interface
    function GetBaseType: string;
    function GetGenerics: TList<IGenericClassName>;
    function GetIsGeneric: Boolean;
    property BaseType: string read GetBaseType;
    property Generics: TList<IGenericClassName> read GetGenerics;
    property IsGeneric: Boolean read GetIsGeneric;
    function ToString: string;
  end;

  TGenericClassName = class(TInterfacedObject, IGenericClassName)
  private
    FBaseType: string;
    FGenerics: TList<IGenericClassName>;

    function GetBaseType: string;
    function GetGenerics: TList<IGenericClassName>;
    function GetIsGeneric: Boolean;
  public
    constructor Create(typ: string);
    destructor Destroy(); override;
    function ToString: string; override;
    property BaseType: string read GetBaseType;
    property Generics: TList<IGenericClassName> read GetGenerics;
    property IsGeneric: Boolean read GetIsGeneric;
  end;

{$IFDEF SUPER_METHOD}

  TSuperMethod = procedure(const This, Params: ISuperObject; var Result: ISuperObject);
{$ENDIF}
  TSuperAvlBitArray = set of 0 .. SUPER_AVL_MAX_DEPTH - 1;

  TSuperAvlSearchType = (stEQual, stLess, stGreater);
  TSuperAvlSearchTypes = set of TSuperAvlSearchType;
  TSuperAvlIterator = class;

  TSuperAvlEntry = class
  private
    FGt, FLt: TSuperAvlEntry;
    FBf: Integer;
    FHash: Cardinal;
    FName: SOString;
    FPtr: Pointer;
    function Getvalue: ISuperObject;
    procedure Setvalue(const val: ISuperObject);
  public
    class function Hash(const k: SOString): Cardinal; virtual;
    constructor Create(const AName: SOString; Obj: Pointer); virtual;
    property Name: SOString read FName;
    property Ptr: Pointer read FPtr;
    property value: ISuperObject read Getvalue write Setvalue;
  end;

  TSuperAvlTree = class
  private
    FRoot: TSuperAvlEntry;
    FCount: Integer;
    function balance(bal: TSuperAvlEntry): TSuperAvlEntry;
  protected
    procedure doDeleteEntry(Entry: TSuperAvlEntry; all: Boolean); virtual;
    function CompareNodeNode(node1, node2: TSuperAvlEntry): Integer; virtual;
    function CompareKeyNode(const k: SOString; h: TSuperAvlEntry): Integer; virtual;
    function Insert(h: TSuperAvlEntry): TSuperAvlEntry; virtual;
    function Search(const k: SOString; st: TSuperAvlSearchTypes = [stEQual]): TSuperAvlEntry; virtual;
  public
    constructor Create; virtual;
    destructor Destroy; override;
    function IsEmpty: Boolean;
    procedure Clear(all: Boolean = false); virtual;
    procedure Pack(all: Boolean);
    function Delete(const k: SOString): ISuperObject;
    function GetEnumerator: TSuperAvlIterator;
    property count: Integer read FCount;
  end;

  TSuperTableString = class(TSuperAvlTree)
  protected
    procedure doDeleteEntry(Entry: TSuperAvlEntry; all: Boolean); override;
    procedure PutO(const k: SOString; const value: ISuperObject);
    function GetO(const k: SOString): ISuperObject;
    procedure PutS(const k: SOString; const value: SOString);
    function GetS(const k: SOString): SOString;
    procedure PutI(const k: SOString; value: SuperInt);
    function GetI(const k: SOString): SuperInt;
    procedure PutD(const k: SOString; value: Double);
    function GetD(const k: SOString): Double;
    procedure PutB(const k: SOString; value: Boolean);
    function GetB(const k: SOString): Boolean;
{$IFDEF SUPER_METHOD}
    procedure PutM(const k: SOString; value: TSuperMethod);
    function GetM(const k: SOString): TSuperMethod;
{$ENDIF}
    procedure PutN(const k: SOString; const value: ISuperObject);
    function GetN(const k: SOString): ISuperObject;
    procedure PutC(const k: SOString; value: Currency);
    function GetC(const k: SOString): Currency;
  public
    property O[const k: SOString]: ISuperObject read GetO write PutO; default;
    property S[const k: SOString]: SOString read GetS write PutS;
    property I[const k: SOString]: SuperInt read GetI write PutI;
    property D[const k: SOString]: Double read GetD write PutD;
    property B[const k: SOString]: Boolean read GetB write PutB;
{$IFDEF SUPER_METHOD}
    property M[const k: SOString]: TSuperMethod read GetM write PutM;
{$ENDIF}
    property N[const k: SOString]: ISuperObject read GetN write PutN;
    property C[const k: SOString]: Currency read GetC write PutC;

    function Getvalues: ISuperObject;
    function GetNames: ISuperObject;
    function Find(const k: SOString; var value: ISuperObject): Boolean;
    function Exists(const k: SOString): Boolean;
  end;

  TSuperAvlIterator = class
  private
    FTree: TSuperAvlTree;
    FBranch: TSuperAvlBitArray;
    FDepth: LongInt;
    FPath: array [0 .. SUPER_AVL_MAX_DEPTH - 2] of TSuperAvlEntry;
  public
    constructor Create(tree: TSuperAvlTree); virtual;
    procedure Search(const k: SOString; st: TSuperAvlSearchTypes = [stEQual]);
    procedure First;
    procedure Last;
    function GetIter: TSuperAvlEntry;
    procedure Next;
    procedure Prior;
    // delphi enumerator
    function MoveNext: Boolean;
    property Current: TSuperAvlEntry read GetIter;
  end;

  TSuperObjectArray = array [0 .. (high(Integer) div sizeof(TSuperObject)) - 1] of ISuperObject;
  PSuperObjectArray = ^TSuperObjectArray;

  TSuperArray = class
  private
    FArray: PSuperObjectArray;
    FLength: Integer;
    FSize: Integer;
    procedure Expand(max: Integer);
  protected
    function GetO(const index: Integer): ISuperObject;
    procedure PutO(const index: Integer; const value: ISuperObject);
    function GetB(const index: Integer): Boolean;
    procedure PutB(const index: Integer; value: Boolean);
    function GetI(const index: Integer): SuperInt;
    procedure PutI(const index: Integer; value: SuperInt);
    function GetD(const index: Integer): Double;
    procedure PutD(const index: Integer; value: Double);
    function GetC(const index: Integer): Currency;
    procedure PutC(const index: Integer; value: Currency);
    function GetS(const index: Integer): SOString;
    procedure PutS(const index: Integer; const value: SOString);
{$IFDEF SUPER_METHOD}
    function GetM(const index: Integer): TSuperMethod;
    procedure PutM(const index: Integer; value: TSuperMethod);
{$ENDIF}
    function GetN(const index: Integer): ISuperObject;
    procedure PutN(const index: Integer; const value: ISuperObject);
  public
    constructor Create; virtual;
    destructor Destroy; override;
    function Add(const Data: ISuperObject): Integer; overload;
    function Add(Data: SuperInt): Integer; overload;
    function Add(const Data: SOString): Integer; overload;
    function Add(Data: Boolean): Integer; overload;
    function Add(Data: Double): Integer; overload;
    function AddC(const Data: Currency): Integer;
    function Delete(index: Integer): ISuperObject;
    procedure Insert(index: Integer; const value: ISuperObject);
    procedure Clear(all: Boolean = false);
    procedure Pack(all: Boolean);
    property Length: Integer read FLength;

    property N[const index: Integer]: ISuperObject read GetN write PutN;
    property O[const index: Integer]: ISuperObject read GetO write PutO; default;
    property B[const index: Integer]: Boolean read GetB write PutB;
    property I[const index: Integer]: SuperInt read GetI write PutI;
    property D[const index: Integer]: Double read GetD write PutD;
    property C[const index: Integer]: Currency read GetC write PutC;
    property S[const index: Integer]: SOString read GetS write PutS;
{$IFDEF SUPER_METHOD}
    property M[const index: Integer]: TSuperMethod read GetM write PutM;
{$ENDIF}
  end;

  TSuperWriter = class
  public
    // abstact methods to overide
    function Append(buf: PSOChar; Size: Integer): Integer; overload; virtual; abstract;
    function Append(buf: PSOChar): Integer; overload; virtual; abstract;
    procedure Reset; virtual; abstract;
  end;

  TSuperWriterString = class(TSuperWriter)
  private
    FBuf: PSOChar;
    FBPos: Integer;
    FSize: Integer;
  public
    function Append(buf: PSOChar; Size: Integer): Integer; overload; override;
    function Append(buf: PSOChar): Integer; overload; override;
    procedure Reset; override;
    procedure TrimRight;
    constructor Create; virtual;
    destructor Destroy; override;
    function GetString: SOString;
    property Data: PSOChar read FBuf;
    property Size: Integer read FSize;
    property Position: Integer read FBPos;
  end;

  TSuperWriterStream = class(TSuperWriter)
  private
    FStream: TStream;
  public
    function Append(buf: PSOChar): Integer; override;
    procedure Reset; override;
    constructor Create(AStream: TStream); reintroduce; virtual;
  end;

  TSuperAnsiWriterStream = class(TSuperWriterStream)
  public
    function Append(buf: PSOChar; Size: Integer): Integer; override;
  end;

  TSuperUnicodeWriterStream = class(TSuperWriterStream)
  public
    function Append(buf: PSOChar; Size: Integer): Integer; override;
  end;

  TSuperWriterFake = class(TSuperWriter)
  private
    FSize: Integer;
  public
    function Append(buf: PSOChar; Size: Integer): Integer; override;
    function Append(buf: PSOChar): Integer; override;
    procedure Reset; override;
    constructor Create; reintroduce; virtual;
    property Size: Integer read FSize;
  end;

  TSuperWriterSock = class(TSuperWriter)
  private
    FSocket: LongInt;
    FSize: Integer;
  public
    function Append(buf: PSOChar; Size: Integer): Integer; override;
    function Append(buf: PSOChar): Integer; override;
    procedure Reset; override;
    constructor Create(ASocket: LongInt); reintroduce; virtual;
    property Socket: LongInt read FSocket;
    property Size: Integer read FSize;
  end;

  TSuperTokenizerError = (teSuccess, teContinue, teDepth, teParseEof, teParseUnexpected, teParseNull, teParseBoolean, teParseNumber, teParseArray,
    teParseObjectKeyName, teParseObjectKeySep, teParseObjectvalueSep, teParseString, teParseComment, teEvalObject, teEvalArray, teEvalMethod,
    teEvalInt);

  TSuperTokenerState = (tsEatws, tsStart, tsFinish, tsNull, tsCommentStart, tsComment, tsCommentEol, tsCommentEnd, tsString, tsStringEscape,
    tsIdentifier, tsEscapeUnicode, tsEscapeHexadecimal, tsBoolean, tsNumber, tsArray, tsArrayAdd, tsArraySep, tsObjectFieldStart, tsObjectField,
    tsObjectUnquotedField, tsObjectFieldEnd, tsObjectvalue, tsObjectvalueAdd, tsObjectSep, tsEvalProperty, tsEvalArray, tsEvalMethod, tsParamvalue,
    tsParamPut, tsMethodvalue, tsMethodPut);

  PSuperTokenerSrec = ^TSuperTokenerSrec;

  TSuperTokenerSrec = record
    state, saved_state: TSuperTokenerState;
    Obj: ISuperObject;
    Current: ISuperObject;
    field_name: SOString;
    parent: ISuperObject;
    gparent: ISuperObject;
  end;

  TSuperTokenizer = class
  public
    str: PSOChar;
    pb: TSuperWriterString;
    depth, is_double, floatcount, st_pos, char_offset: Integer;
    err: TSuperTokenizerError;
    ucs_char: Word;
    quote_char: SOChar;
    stack: array [0 .. SUPER_TOKENER_MAX_DEPTH - 1] of TSuperTokenerSrec;
    line, col: Integer;
  public
    constructor Create; virtual;
    destructor Destroy; override;
    procedure ResetLevel(adepth: Integer);
    procedure Reset;
  end;

  // supported object types
  TSuperType = (stNull, stBoolean, stDouble, stCurrency, stInt, stObject, stArray, stString
{$IFDEF SUPER_METHOD}
    , stMethod
{$ENDIF}
    );

  TSuperValidateError = (veRuleMalformated, veFieldIsRequired, veInvalidDataType, veFieldNotFound, veUnexpectedField, veDuplicateEntry,
    vevalueNotInEnum, veInvalidLength, veInvalidRange);

  TSuperFindOption = (foCreatePath, foPutvalue, foDelete
{$IFDEF SUPER_METHOD}
    , foCallMethod
{$ENDIF}
    );

  TSuperFindOptions = set of TSuperFindOption;
  TSuperCompareResult = (cpLess, cpEqu, cpGreat, cpError);
  TSuperOnValidateError = procedure(sender: Pointer; error: TSuperValidateError; const objpath: SOString);

  TSuperEnumerator = class
  private
    FObj: ISuperObject;
    FObjEnum: TSuperAvlIterator;
    FCount: Integer;
  public
    constructor Create(const Obj: ISuperObject); virtual;
    destructor Destroy; override;
    function MoveNext: Boolean;
    function GetCurrent: ISuperObject;
    property Current: ISuperObject read GetCurrent;
  end;

  ISuperObject = interface
    ['{4B86A9E3-E094-4E5A-954A-69048B7B6327}']
    function GetEnumerator: TSuperEnumerator;
    function GetDataType: TSuperType;
    function GetProcessing: Boolean;
    procedure SetProcessing(value: Boolean);
    function ForcePath(const path: SOString; dataType: TSuperType = stObject): ISuperObject;
    function Format(const str: SOString; BeginSep: SOChar = '%'; EndSep: SOChar = '%'): SOString;

    function GetO(const path: SOString): ISuperObject;
    procedure PutO(const path: SOString; const value: ISuperObject);
    function GetB(const path: SOString): Boolean;
    procedure PutB(const path: SOString; value: Boolean);
    function GetI(const path: SOString): SuperInt;
    procedure PutI(const path: SOString; value: SuperInt);
    function GetD(const path: SOString): Double;
    procedure PutC(const path: SOString; value: Currency);
    function GetC(const path: SOString): Currency;
    procedure PutD(const path: SOString; value: Double);
    function GetS(const path: SOString): SOString;
    procedure PutS(const path: SOString; const value: SOString);
{$IFDEF SUPER_METHOD}
    function GetM(const path: SOString): TSuperMethod;
    procedure PutM(const path: SOString; value: TSuperMethod);
{$ENDIF}
    function GetA(const path: SOString): TSuperArray;

    // Null Object Design patern
    function GetN(const path: SOString): ISuperObject;
    procedure PutN(const path: SOString; const value: ISuperObject);

    // Writers
    function Write(writer: TSuperWriter; indent: Boolean; escape: Boolean; level: Integer): Integer;
    function SaveTo(stream: TStream; indent: Boolean = false; escape: Boolean = true): Integer; overload;
    function SaveTo(const FileName: string; indent: Boolean = false; escape: Boolean = true): Integer; overload;
    function SaveTo(Socket: LongInt; indent: Boolean = false; escape: Boolean = true): Integer; overload;
    function CalcSize(indent: Boolean = false; escape: Boolean = true): Integer;

    // convert
    function AsBoolean: Boolean;
    function AsInteger: SuperInt;
    function AsDouble: Double;
    function AsCurrency: Currency;
    function AsString: SOString;
    function AsArray: TSuperArray;
    function AsObject: TSuperTableString;
{$IFDEF SUPER_METHOD}
    function AsMethod: TSuperMethod;
{$ENDIF}
    function AsJSon(indent: Boolean = false; escape: Boolean = true): SOString;

    procedure Clear(all: Boolean = false);
    procedure Pack(all: Boolean = false);

    property N[const path: SOString]: ISuperObject read GetN write PutN;
    property O[const path: SOString]: ISuperObject read GetO write PutO; default;
    property B[const path: SOString]: Boolean read GetB write PutB;
    property I[const path: SOString]: SuperInt read GetI write PutI;
    property D[const path: SOString]: Double read GetD write PutD;
    property C[const path: SOString]: Currency read GetC write PutC;
    property S[const path: SOString]: SOString read GetS write PutS;
{$IFDEF SUPER_METHOD}
    property M[const path: SOString]: TSuperMethod read GetM write PutM;
{$ENDIF}
    property A[const path: SOString]: TSuperArray read GetA;

{$IFDEF SUPER_METHOD}
    function call(const path: SOString; const param: ISuperObject = nil): ISuperObject; overload;
    function call(const path, param: SOString): ISuperObject; overload;
{$ENDIF}
    // clone a node
    function Clone: ISuperObject;
    function Delete(const path: SOString): ISuperObject;
    // merges tow objects of same type, if reference is true then nodes are not cloned
    procedure Merge(const Obj: ISuperObject; reference: Boolean = false); overload;
    procedure Merge(const str: SOString); overload;

    // validate methods
    function Validate(const rules: SOString; const defs: SOString = ''; callback: TSuperOnValidateError = nil; sender: Pointer = nil)
      : Boolean; overload;
    function Validate(const rules: ISuperObject; const defs: ISuperObject = nil; callback: TSuperOnValidateError = nil; sender: Pointer = nil)
      : Boolean; overload;

    // compare
    function Compare(const Obj: ISuperObject): TSuperCompareResult; overload;
    function Compare(const str: SOString): TSuperCompareResult; overload;

    // the data type
    function IsType(AType: TSuperType): Boolean;
    property dataType: TSuperType read GetDataType;
    property Processing: Boolean read GetProcessing write SetProcessing;

    function GetDataPtr: Pointer;
    procedure SetDataPtr(const value: Pointer);
    property DataPtr: Pointer read GetDataPtr write SetDataPtr;
  end;

  TSuperObject = class(TObject, ISuperObject)
  private
    FRefCount: Integer;
    FProcessing: Boolean;
    FDataType: TSuperType;
    FDataPtr: Pointer;

    { .$if true }
    FO: record
      case TSuperType of
        stBoolean:
          (c_Boolean: Boolean);
        stDouble:
          (c_double: Double);
        stCurrency:
          (c_currency: Currency);
        stInt:
          (c_int: SuperInt);
        stObject:
          (c_object: TSuperTableString);
        stArray:
          (c_array: TSuperArray);
{$IFDEF SUPER_METHOD}
        stMethod:
          (c_method: TSuperMethod);
{$ENDIF}
    end;

    { .$ifend }
    FOString: SOString;
    function GetDataType: TSuperType;
    function GetDataPtr: Pointer;
    procedure SetDataPtr(const value: Pointer);
  protected
{$IFDEF FPC}
    function QueryInterface({$IFDEF FPC_HAS_CONSTREF}constref{$ELSE}const {$ENDIF} iid: tguid; out Obj): LongInt; {$IFNDEF WINDOWS}cdecl{$ELSE}stdcall{$ENDIF};
{$ELSE}
    function QueryInterface(const iid: tguid; out Obj): HResult; virtual; stdcall;
{$ENDIF}
    function _AddRef: Integer; virtual; stdcall;
    function _Release: Integer; virtual; stdcall;

    function GetO(const path: SOString): ISuperObject;
    procedure PutO(const path: SOString; const value: ISuperObject);
    function GetB(const path: SOString): Boolean;
    procedure PutB(const path: SOString; value: Boolean);
    function GetI(const path: SOString): SuperInt;
    procedure PutI(const path: SOString; value: SuperInt);
    function GetD(const path: SOString): Double;
    procedure PutD(const path: SOString; value: Double);
    procedure PutC(const path: SOString; value: Currency);
    function GetC(const path: SOString): Currency;
    function GetS(const path: SOString): SOString;
    procedure PutS(const path: SOString; const value: SOString);
{$IFDEF SUPER_METHOD}
    function GetM(const path: SOString): TSuperMethod;
    procedure PutM(const path: SOString; value: TSuperMethod);
{$ENDIF}
    function GetA(const path: SOString): TSuperArray;
    function Write(writer: TSuperWriter; indent: Boolean; escape: Boolean; level: Integer): Integer; virtual;
  public
    function GetEnumerator: TSuperEnumerator;
    procedure AfterConstruction; override;
    procedure BeforeDestruction; override;
    class function NewInstance: TObject; override;
    property RefCount: Integer read FRefCount;

    function GetProcessing: Boolean;
    procedure SetProcessing(value: Boolean);

    // Writers
    function SaveTo(stream: TStream; indent: Boolean = false; escape: Boolean = true): Integer; overload;
    function SaveTo(const FileName: string; indent: Boolean = false; escape: Boolean = true): Integer; overload;
    function SaveTo(Socket: LongInt; indent: Boolean = false; escape: Boolean = true): Integer; overload;
    function CalcSize(indent: Boolean = false; escape: Boolean = true): Integer;
    function AsJSon(indent: Boolean = false; escape: Boolean = true): SOString;

    // parser  ... owned!
    class function ParseString(S: PSOChar; strict: Boolean; partial: Boolean = true; const This: ISuperObject = nil; options: TSuperFindOptions = [];
      const put: ISuperObject = nil; dt: TSuperType = stNull): ISuperObject;
    class function ParseStream(stream: TStream; strict: Boolean; partial: Boolean = true; const This: ISuperObject = nil;
      options: TSuperFindOptions = []; const put: ISuperObject = nil; dt: TSuperType = stNull): ISuperObject;
    class function ParseFile(const FileName: string; strict: Boolean; partial: Boolean = true; const This: ISuperObject = nil;
      options: TSuperFindOptions = []; const put: ISuperObject = nil; dt: TSuperType = stNull): ISuperObject;
    class function ParseEx(tok: TSuperTokenizer; str: PSOChar; len: Integer; strict: Boolean; const This: ISuperObject = nil;
      options: TSuperFindOptions = []; const put: ISuperObject = nil; dt: TSuperType = stNull): ISuperObject;

    // constructors / destructor
    constructor Create(jt: TSuperType = stObject); overload; virtual;
    constructor Create(B: Boolean); overload; virtual;
    constructor Create(I: SuperInt); overload; virtual;
    constructor Create(D: Double); overload; virtual;
    constructor CreateCurrency(C: Currency); overload; virtual;
    constructor Create(const S: SOString); overload; virtual;
{$IFDEF SUPER_METHOD}
    constructor Create(M: TSuperMethod); overload; virtual;
{$ENDIF}
    destructor Destroy; override;

    // convert
    function AsBoolean: Boolean; virtual;
    function AsInteger: SuperInt; virtual;
    function AsDouble: Double; virtual;
    function AsCurrency: Currency; virtual;
    function AsString: SOString; virtual;
    function AsArray: TSuperArray; virtual;
    function AsObject: TSuperTableString; virtual;
{$IFDEF SUPER_METHOD}
    function AsMethod: TSuperMethod; virtual;
{$ENDIF}
    procedure Clear(all: Boolean = false); virtual;
    procedure Pack(all: Boolean = false); virtual;
    function GetN(const path: SOString): ISuperObject;
    procedure PutN(const path: SOString; const value: ISuperObject);
    function ForcePath(const path: SOString; dataType: TSuperType = stObject): ISuperObject;
    function Format(const str: SOString; BeginSep: SOChar = '%'; EndSep: SOChar = '%'): SOString;

    property N[const path: SOString]: ISuperObject read GetN write PutN;
    property O[const path: SOString]: ISuperObject read GetO write PutO; default;
    property B[const path: SOString]: Boolean read GetB write PutB;
    property I[const path: SOString]: SuperInt read GetI write PutI;
    property D[const path: SOString]: Double read GetD write PutD;
    property C[const path: SOString]: Currency read GetC write PutC;
    property S[const path: SOString]: SOString read GetS write PutS;
{$IFDEF SUPER_METHOD}
    property M[const path: SOString]: TSuperMethod read GetM write PutM;
{$ENDIF}
    property A[const path: SOString]: TSuperArray read GetA;

{$IFDEF SUPER_METHOD}
    function call(const path: SOString; const param: ISuperObject = nil): ISuperObject; overload; virtual;
    function call(const path, param: SOString): ISuperObject; overload; virtual;
{$ENDIF}
    // clone a node
    function Clone: ISuperObject; virtual;
    function Delete(const path: SOString): ISuperObject;
    // merges tow objects of same type, if reference is true then nodes are not cloned
    procedure Merge(const Obj: ISuperObject; reference: Boolean = false); overload;
    procedure Merge(const str: SOString); overload;

    // validate methods
    function Validate(const rules: SOString; const defs: SOString = ''; callback: TSuperOnValidateError = nil; sender: Pointer = nil)
      : Boolean; overload;
    function Validate(const rules: ISuperObject; const defs: ISuperObject = nil; callback: TSuperOnValidateError = nil; sender: Pointer = nil)
      : Boolean; overload;

    // compare
    function Compare(const Obj: ISuperObject): TSuperCompareResult; overload;
    function Compare(const str: SOString): TSuperCompareResult; overload;

    // the data type
    function IsType(AType: TSuperType): Boolean;
    property dataType: TSuperType read GetDataType;
    // a data pointer to link to something ele, a treeview for example
    property DataPtr: Pointer read GetDataPtr write SetDataPtr;
    property Processing: Boolean read GetProcessing;
  end;

{$IFDEF HAVE_RTTI}

  TSuperRttiContext = class;

  TSerialFromJson = function(ctx: TSuperRttiContext; const Obj: ISuperObject; var value: Tvalue): Boolean;
  TSerialToJson = function(ctx: TSuperRttiContext; var value: Tvalue; const index: ISuperObject): ISuperObject;

  TSuperAttribute = class(TCustomAttribute)
  private
    FName: string;
  public
    constructor Create(const AName: string);
    property Name: string read FName;
  end;

  SOName = class(TSuperAttribute);
  SODefault = class(TSuperAttribute);

  TSuperRttiContext = class
  private
    class function GetFieldName(r: TRttiField): string;
    class function GetFieldDefault(r: TRttiField; const Obj: ISuperObject): ISuperObject;

  public
    Context: TRttiContext;
    SerialFromJson: TDictionary<PTypeInfo, TSerialFromJson>;
    SerialToJson: TDictionary<PTypeInfo, TSerialToJson>;
    constructor Create; virtual;
    destructor Destroy; override;
    function FromJson(TypeInfo: PTypeInfo; const Obj: ISuperObject; var value: Tvalue): Boolean; virtual;
    function ToJson(var value: Tvalue; const index: ISuperObject): ISuperObject; virtual;
    function AsType<T>(const Obj: ISuperObject): T;
    function AsJSon<T>(const Obj: T; const index: ISuperObject = nil): ISuperObject;
  end;

  TSuperObjectHelper = class helper for TObject
  public
    function ToJson(ctx: TSuperRttiContext = nil): ISuperObject;
    constructor FromJson(const Obj: ISuperObject; ctx: TSuperRttiContext = nil); overload;
    constructor FromJson(const str: string; ctx: TSuperRttiContext = nil); overload;
  end;
{$ENDIF}

  TSuperObjectIter = record
    key: SOString;
    val: ISuperObject;
    Ite: TSuperAvlIterator;
  end;

function ObjectIsError(Obj: TSuperObject): Boolean;
function ObjectIsType(const Obj: ISuperObject; typ: TSuperType): Boolean;
function ObjectGetType(const Obj: ISuperObject): TSuperType;
function ObjectIsNull(const Obj: ISuperObject): Boolean;

function ObjectFindFirst(const Obj: ISuperObject; var F: TSuperObjectIter): Boolean;
function ObjectFindNext(var F: TSuperObjectIter): Boolean;
procedure ObjectFindClose(var F: TSuperObjectIter);

function SO(const S: SOString = '{}'): ISuperObject; overload;
function SO(const value: Variant): ISuperObject; overload;
function SO(const Args: array of const): ISuperObject; overload;

function SA(const Args: array of const): ISuperObject; overload;

function TryObjectToDate(const Obj: ISuperObject; var dt: TDateTime): Boolean;
function UUIDToString(const g: tguid): SOString;
function StringToUUID(const str: SOString; var g: tguid): Boolean;

{$IFDEF HAVE_RTTI}

type
  TSuperInvokeResult = (irSuccess, irMethothodError, // method don't exist
    irParamError, // invalid parametters
    irError // other error
    );

function TrySOInvoke(var ctx: TSuperRttiContext; const Obj: Tvalue; const method: string; const Params: ISuperObject; var Return: ISuperObject)
  : TSuperInvokeResult; overload;
function SOInvoke(const Obj: Tvalue; const method: string; const Params: ISuperObject; ctx: TSuperRttiContext = nil): ISuperObject; overload;
function SOInvoke(const Obj: Tvalue; const method: string; const Params: string; ctx: TSuperRttiContext = nil): ISuperObject; overload;
{$ENDIF}

implementation

uses
  sysutils, Windows, superdate
{$IFDEF FPC}
    , sockets
{$ELSE}
    , WinSock
{$ENDIF}
    ;

type
  TTypeInfoCache = class
  private
    FTypes: TDictionary<string, TRttiType>;
    class var FInstance: TTypeInfoCache;
    constructor Create();
    class destructor Destroy;
  public
    class function Instance: TTypeInfoCache;
    function get(name: string): TRttiType;
  end;

constructor TTypeInfoCache.Create();
var
  Context: TRttiContext;
  T: TRttiType;
begin
  FTypes := TDictionary<string, TRttiType>.Create;
  Context := TRttiContext.Create;
  try
    for T in Context.gettypes do
    begin
      FTypes.AddOrSetValue(lowercase(T.name), T);
    end;
  finally
    Context.free;
  end;
end;

function TTypeInfoCache.get(name: string): TRttiType;
begin
  if not FTypes.trygetvalue(name, Result) then
    Result := nil;
end;

class destructor TTypeInfoCache.Destroy;
begin
  inherited;
end;

class function TTypeInfoCache.Instance: TTypeInfoCache;
begin
  if FInstance = nil then
    FInstance := TTypeInfoCache.Create();
  Result := FInstance;
end;

{$IFDEF DEBUG}

var
  debugcount: Integer = 0;
{$ENDIF}

const
  super_number_chars_set = ['0' .. '9', '.', '+', '-', 'e', 'E'];
  super_hex_chars: PSOChar = '0123456789abcdef';
  super_hex_chars_set = ['0' .. '9', 'a' .. 'f', 'A' .. 'F'];

  ESC_BS: PSOChar = '\b';
  ESC_LF: PSOChar = '\n';
  ESC_CR: PSOChar = '\r';
  ESC_TAB: PSOChar = '\t';
  ESC_FF: PSOChar = '\f';
  ESC_QUOT: PSOChar = '\"';
  ESC_SL: PSOChar = '\\';
  ESC_SR: PSOChar = '\/';
  ESC_ZERO: PSOChar = '\u0000';

  TOK_CRLF: PSOChar = #13#10;
  TOK_SP: PSOChar = #32;
  TOK_BS: PSOChar = #8;
  TOK_TAB: PSOChar = #9;
  TOK_LF: PSOChar = #10;
  TOK_FF: PSOChar = #12;
  TOK_CR: PSOChar = #13;
  // TOK_SL: PSOChar = '\';
  // TOK_SR: PSOChar = '/';
  TOK_NULL: PSOChar = 'null';
  TOK_CBL: PSOChar = '{'; // curly bracket left
  TOK_CBR: PSOChar = '}'; // curly bracket right
  TOK_ARL: PSOChar = '[';
  TOK_ARR: PSOChar = ']';
  TOK_ARRAY: PSOChar = '[]';
  TOK_OBJ: PSOChar = '{}'; // empty object
  TOK_COM: PSOChar = ','; // Comma
  TOK_DQT: PSOChar = '"'; // Double Quote
  TOK_TRUE: PSOChar = 'true';
  TOK_FALSE: PSOChar = 'false';

{$IF (sizeof(Char) = 1)}

function StrLComp(const Str1, Str2: PSOChar; MaxLen: Cardinal): Integer;
var
  P1, P2: PWideChar;
  I: Cardinal;
  C1, C2: WideChar;
begin
  P1 := Str1;
  P2 := Str2;
  I := 0;
  while I < MaxLen do
  begin
    C1 := P1^;
    C2 := P2^;

    if (C1 <> C2) or (C1 = #0) then
    begin
      Result := Ord(C1) - Ord(C2);
      Exit;
    end;

    Inc(P1);
    Inc(P2);
    Inc(I);
  end;
  Result := 0;
end;

function StrComp(const Str1, Str2: PSOChar): Integer;
var
  P1, P2: PWideChar;
  C1, C2: WideChar;
begin
  P1 := Str1;
  P2 := Str2;
  while true do
  begin
    C1 := P1^;
    C2 := P2^;

    if (C1 <> C2) or (C1 = #0) then
    begin
      Result := Ord(C1) - Ord(C2);
      Exit;
    end;

    Inc(P1);
    Inc(P2);
  end;
end;

function StrLen(const str: PSOChar): Cardinal;
var
  p: PSOChar;
begin
  Result := 0;
  if str <> nil then
  begin
    p := str;
    while p^ <> #0 do
      Inc(p);
    Result := (p - str);
  end;
end;
{$IFEND}

function FloatToJson(const value: Double): SOString;
var
  p: PSOChar;
begin
  Result := FloatToStr(value);
  if {$IF defined(NEED_FORMATSETTINGS)}FormatSettings.{$ENDIF}DecimalSeparator <> '.' then
  begin
    p := PSOChar(Result);
    while p^ <> #0 do
      if p^ <> SOChar({$IF defined(NEED_FORMATSETTINGS)}FormatSettings.{$ENDIF}DecimalSeparator) then
        Inc(p)
      else
      begin
        p^ := '.';
        Exit;
      end;
  end;
end;

function CurrToJson(const value: Currency): SOString;
var
  p: PSOChar;
begin
  Result := CurrToStr(value);
  if {$IF defined(NEED_FORMATSETTINGS)}FormatSettings.{$ENDIF}DecimalSeparator <> '.' then
  begin
    p := PSOChar(Result);
    while p^ <> #0 do
      if p^ <> SOChar({$IF defined(NEED_FORMATSETTINGS)}FormatSettings.{$ENDIF}DecimalSeparator) then
        Inc(p)
      else
      begin
        p^ := '.';
        Exit;
      end;
  end;
end;

function TryObjectToDate(const Obj: ISuperObject; var dt: TDateTime): Boolean;
var
  I: Int64;
begin
  case ObjectGetType(Obj) of
    stInt:
      begin
        dt := JavaToDelphiDateTime(Obj.AsInteger);
        Result := true;
      end;
    stString:
      begin
        if ISO8601DateToJavaDateTime(Obj.AsString, I) then
        begin
          dt := JavaToDelphiDateTime(I);
          Result := true;
        end
        else
          Result := TryStrToDateTime(Obj.AsString, dt);
      end;
  else
    Result := false;
  end;
end;

function SO(const S: SOString): ISuperObject; overload;
begin
  Result := TSuperObject.ParseString(PSOChar(S), false);
end;

function SA(const Args: array of const): ISuperObject; overload;
type
  TByteArray = array [0 .. sizeof(Integer) - 1] of byte;
  PByteArray = ^TByteArray;
var
  j: Integer;
  intf: IInterface;
begin
  Result := TSuperObject.Create(stArray);
  for j := 0 to Length(Args) - 1 do
    with Result.AsArray do
      case TVarRec(Args[j]).VType of
        vtInteger:
          Add(TSuperObject.Create(TVarRec(Args[j]).VInteger));
        vtInt64:
          Add(TSuperObject.Create(TVarRec(Args[j]).VInt64^));
        vtBoolean:
          Add(TSuperObject.Create(TVarRec(Args[j]).VBoolean));
        vtChar:
          Add(TSuperObject.Create(SOString(TVarRec(Args[j]).VChar)));
        vtWideChar:
          Add(TSuperObject.Create(SOChar(TVarRec(Args[j]).VWideChar)));
        vtExtended:
          Add(TSuperObject.Create(TVarRec(Args[j]).VExtended^));
        vtCurrency:
          Add(TSuperObject.CreateCurrency(TVarRec(Args[j]).VCurrency^));
        vtString:
          Add(TSuperObject.Create(SOString(TVarRec(Args[j]).VString^)));
        vtPChar:
          Add(TSuperObject.Create(SOString(TVarRec(Args[j]).VPChar^)));
        vtAnsiString:
          Add(TSuperObject.Create(SOString(AnsiString(TVarRec(Args[j]).VAnsiString))));
        vtWideString:
          Add(TSuperObject.Create(SOString(PWideChar(TVarRec(Args[j]).VWideString))));
        vtInterface:
          if TVarRec(Args[j]).VInterface = nil then
            Add(nil)
          else if IInterface(TVarRec(Args[j]).VInterface).QueryInterface(ISuperObject, intf) = 0 then
            Add(ISuperObject(intf))
          else
            Add(nil);
        vtPointer:
          if TVarRec(Args[j]).VPointer = nil then
            Add(nil)
          else
            Add(TSuperObject.Create(PtrInt(TVarRec(Args[j]).VPointer)));
        vtVariant:
          Add(SO(TVarRec(Args[j]).VVariant^));
        vtObject:
          if TVarRec(Args[j]).VPointer = nil then
            Add(nil)
          else
            Add(TSuperObject.Create(PtrInt(TVarRec(Args[j]).VPointer)));
        vtClass:
          if TVarRec(Args[j]).VPointer = nil then
            Add(nil)
          else
            Add(TSuperObject.Create(PtrInt(TVarRec(Args[j]).VPointer)));
{$IF declared(vtUnicodeString)}
        vtUnicodeString:
          Add(TSuperObject.Create(SOString(string(TVarRec(Args[j]).VUnicodeString))));
{$ENDIF}
      else
        assert(false);
      end;
end;

function SO(const Args: array of const): ISuperObject; overload;
var
  j: Integer;
  arr: ISuperObject;
begin
  Result := TSuperObject.Create(stObject);
  arr := SA(Args);
  with arr.AsArray do
    for j := 0 to (Length div 2) - 1 do
      Result.AsObject.PutO(O[j * 2].AsString, O[(j * 2) + 1]);
end;

function SO(const value: Variant): ISuperObject; overload;
begin
  with TVarData(value) do
    case VType of
      varNull:
        Result := nil;
      varEmpty:
        Result := nil;
      varSmallInt:
        Result := TSuperObject.Create(VSmallInt);
      varInteger:
        Result := TSuperObject.Create(VInteger);
      varSingle:
        Result := TSuperObject.Create(VSingle);
      varDouble:
        Result := TSuperObject.Create(VDouble);
      varCurrency:
        Result := TSuperObject.CreateCurrency(VCurrency);
      varDate:
        Result := TSuperObject.Create(DelphiToJavaDateTime(vDate));
      varOleStr:
        Result := TSuperObject.Create(SOString(VOleStr));
      varBoolean:
        Result := TSuperObject.Create(VBoolean);
      varShortInt:
        Result := TSuperObject.Create(VShortInt);
      varByte:
        Result := TSuperObject.Create(VByte);
      varWord:
        Result := TSuperObject.Create(VWord);
      varLongWord:
        Result := TSuperObject.Create(VLongWord);
      varInt64:
        Result := TSuperObject.Create(VInt64);
      varString:
        Result := TSuperObject.Create(SOString(AnsiString(VString)));
{$IF declared(varUString)}
{$IFDEF FPC}
      varUString:
        Result := TSuperObject.Create(SOString(UnicodeString(VString)));
{$ELSE}
      varUString:
        Result := TSuperObject.Create(SOString(string(VUString)));
{$ENDIF}
{$ENDIF}
    else
      raise Exception.CreateFmt('Unsuported variant data type: %d', [VType]);
    end;
end;

function ObjectIsError(Obj: TSuperObject): Boolean;
begin
  Result := PtrUInt(Obj) > PtrUInt(-4000);
end;

function ObjectIsType(const Obj: ISuperObject; typ: TSuperType): Boolean;
begin
  if Obj <> nil then
    Result := typ = Obj.dataType
  else
    Result := typ = stNull;
end;

function ObjectGetType(const Obj: ISuperObject): TSuperType;
begin
  if Obj <> nil then
    Result := Obj.dataType
  else
    Result := stNull;
end;

function ObjectIsNull(const Obj: ISuperObject): Boolean;
begin
  Result := ObjectIsType(Obj, stNull);
end;

function ObjectFindFirst(const Obj: ISuperObject; var F: TSuperObjectIter): Boolean;
var
  I: TSuperAvlEntry;
begin
  if ObjectIsType(Obj, stObject) then
  begin
    F.Ite := TSuperAvlIterator.Create(Obj.AsObject);
    F.Ite.First;
    I := F.Ite.GetIter;
    if I <> nil then
    begin
      F.key := I.name;
      F.val := I.value;
      Result := true;
    end
    else
    begin
      FreeAndNil(F.Ite);
      Result := false;
    end;
  end
  else
    Result := false;
end;

function ObjectFindNext(var F: TSuperObjectIter): Boolean;
var
  I: TSuperAvlEntry;
begin
  if Assigned(F.Ite) then
  begin
    F.Ite.Next;
    I := F.Ite.GetIter;
    if I <> nil then
    begin
      F.key := I.FName;
      F.val := I.value;
      Result := true;
    end
    else
      Result := false;
  end
  else
    Result := false;
end;

procedure ObjectFindClose(var F: TSuperObjectIter);
begin
  if Assigned(F.Ite) then
    FreeAndNil(F.Ite);
  F.val := nil;
end;

function UuidFromString(p: PSOChar; Uuid: PGUID): Boolean;
const
  hex2bin: array [48 .. 102] of byte = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0, 0, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 11, 12, 13, 14, 15);
type
  TState = (stEatSpaces, stStart, stHEX, stBracket, stEnd);

  TUUID = record
    case byte of
      0:
        (guid: tguid);
      1:
        (bytes: array [0 .. 15] of byte);
      2:
        (words: array [0 .. 7] of Word);
      3:
        (ints: array [0 .. 3] of Cardinal);
      4:
        (i64s: array [0 .. 1] of UInt64);
  end;

  function ishex(const C: SOChar): Boolean; {$IFDEF HAVE_INLINE} inline; {$ENDIF}
  begin
    Result := (C < #256) and (AnsiChar(C) in ['0' .. '9', 'a' .. 'z', 'A' .. 'Z'])
  end;

var
  pos: byte;
  state, saved: TState;
  bracket, separator: Boolean;
label
  redo;
begin
  FillChar(Uuid^, sizeof(tguid), 0);
  saved := stStart;
  state := stEatSpaces;
  bracket := false;
  separator := false;
  pos := 0;
  while true do
  redo:
    case state of
      stEatSpaces:
        begin
          while true do
            case p^ of
              ' ', #13, #10, #9:
                Inc(p);
            else
              state := saved;
              goto redo;
            end;
        end;
      stStart:
        case p^ of
          '{':
            begin
              bracket := true;
              Inc(p);
              state := stEatSpaces;
              saved := stHEX;
              pos := 0;
            end;
        else
          state := stHEX;
        end;
      stHEX:
        case pos of
          0 .. 7:
            if ishex(p^) then
            begin
              Uuid^.D1 := (Uuid^.D1 * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          8:
            if (p^ = '-') then
            begin
              separator := true;
              Inc(p);
              Inc(pos)
            end
            else
              Inc(pos);
          13, 18, 23:
            if separator then
            begin
              if p^ <> '-' then
              begin
                Result := false;
                Exit;
              end;
              Inc(p);
              Inc(pos);
            end
            else
              Inc(pos);
          9 .. 12:
            if ishex(p^) then
            begin
              TUUID(Uuid^).words[2] := (TUUID(Uuid^).words[2] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          14 .. 17:
            if ishex(p^) then
            begin
              TUUID(Uuid^).words[3] := (TUUID(Uuid^).words[3] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          19 .. 20:
            if ishex(p^) then
            begin
              TUUID(Uuid^).bytes[8] := (TUUID(Uuid^).bytes[8] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          21 .. 22:
            if ishex(p^) then
            begin
              TUUID(Uuid^).bytes[9] := (TUUID(Uuid^).bytes[9] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          24 .. 25:
            if ishex(p^) then
            begin
              TUUID(Uuid^).bytes[10] := (TUUID(Uuid^).bytes[10] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          26 .. 27:
            if ishex(p^) then
            begin
              TUUID(Uuid^).bytes[11] := (TUUID(Uuid^).bytes[11] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          28 .. 29:
            if ishex(p^) then
            begin
              TUUID(Uuid^).bytes[12] := (TUUID(Uuid^).bytes[12] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          30 .. 31:
            if ishex(p^) then
            begin
              TUUID(Uuid^).bytes[13] := (TUUID(Uuid^).bytes[13] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          32 .. 33:
            if ishex(p^) then
            begin
              TUUID(Uuid^).bytes[14] := (TUUID(Uuid^).bytes[14] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          34 .. 35:
            if ishex(p^) then
            begin
              TUUID(Uuid^).bytes[15] := (TUUID(Uuid^).bytes[15] * 16) + hex2bin[Ord(p^)];
              Inc(p);
              Inc(pos);
            end
            else
            begin
              Result := false;
              Exit;
            end;
          36:
            if bracket then
            begin
              state := stEatSpaces;
              saved := stBracket;
            end
            else
            begin
              state := stEatSpaces;
              saved := stEnd;
            end;
        end;
      stBracket:
        begin
          if p^ <> '}' then
          begin
            Result := false;
            Exit;
          end;
          Inc(p);
          state := stEatSpaces;
          saved := stEnd;
        end;
      stEnd:
        begin
          if p^ <> #0 then
          begin
            Result := false;
            Exit;
          end;
          Break;
        end;
    end;
  Result := true;
end;

function UUIDToString(const g: tguid): SOString;
begin
  Result := Format('%.8x%.4x%.4x%.2x%.2x%.2x%.2x%.2x%.2x%.2x%.2x', [g.D1, g.D2, g.D3, g.D4[0], g.D4[1], g.D4[2], g.D4[3], g.D4[4], g.D4[5], g.D4[6],
    g.D4[7]]);
end;

function StringToUUID(const str: SOString; var g: tguid): Boolean;
begin
  Result := UuidFromString(PSOChar(str), @g);
end;

{$IFDEF HAVE_RTTI}

function serialtoBoolean(ctx: TSuperRttiContext; var value: Tvalue; const index: ISuperObject): ISuperObject;
begin
  Result := TSuperObject.Create(TvalueData(value).FAsSLong <> 0);
end;

function serialtodatetime(ctx: TSuperRttiContext; var value: Tvalue; const index: ISuperObject): ISuperObject;
begin
  Result := TSuperObject.Create(DelphiToJavaDateTime(TvalueData(value).FAsDouble));
end;

function serialtoguid(ctx: TSuperRttiContext; var value: Tvalue; const index: ISuperObject): ISuperObject;
var
  g: tguid;
begin
  value.ExtractRawData(@g);
  Result := TSuperObject.Create(Format('%.8x-%.4x-%.4x-%.2x%.2x-%.2x%.2x%.2x%.2x%.2x%.2x', [g.D1, g.D2, g.D3, g.D4[0], g.D4[1], g.D4[2], g.D4[3],
    g.D4[4], g.D4[5], g.D4[6], g.D4[7]]));
end;

function serialfromBoolean(ctx: TSuperRttiContext; const Obj: ISuperObject; var value: Tvalue): Boolean;
var
  O: ISuperObject;
begin
  case ObjectGetType(Obj) of
    stBoolean:
      begin
        TvalueData(value).FAsSLong := Obj.AsInteger;
        Result := true;
      end;
    stInt:
      begin
        TvalueData(value).FAsSLong := Ord(Obj.AsInteger <> 0);
        Result := true;
      end;
    stString:
      begin
        O := SO(Obj.AsString);
        if not ObjectIsType(O, stString) then
          Result := serialfromBoolean(ctx, SO(Obj.AsString), value)
        else
          Result := false;
      end;
  else
    Result := false;
  end;
end;

function serialfromdatetime(ctx: TSuperRttiContext; const Obj: ISuperObject; var value: Tvalue): Boolean;
var
  dt: TDateTime;
  I: Int64;
begin
  case ObjectGetType(Obj) of
    stInt:
      begin
        TvalueData(value).FAsDouble := JavaToDelphiDateTime(Obj.AsInteger);
        Result := true;
      end;
    stString:
      begin
        if ISO8601DateToJavaDateTime(Obj.AsString, I) then
        begin
          TvalueData(value).FAsDouble := JavaToDelphiDateTime(I);
          Result := true;
        end
        else if TryStrToDateTime(Obj.AsString, dt) then
        begin
          TvalueData(value).FAsDouble := dt;
          Result := true;
        end
        else
          Result := false;
      end;
  else
    Result := false;
  end;
end;

function serialfromguid(ctx: TSuperRttiContext; const Obj: ISuperObject; var value: Tvalue): Boolean;
begin
  case ObjectGetType(Obj) of
    stNull:
      begin
        FillChar(value.GetReferenceToRawData^, sizeof(tguid), 0);
        Result := true;
      end;
    stString:
      Result := UuidFromString(PSOChar(Obj.AsString), value.GetReferenceToRawData);
  else
    Result := false;
  end;
end;

function SOInvoke(const Obj: Tvalue; const method: string; const Params: ISuperObject; ctx: TSuperRttiContext): ISuperObject; overload;
var
  owned: Boolean;
begin
  if ctx = nil then
  begin
    ctx := TSuperRttiContext.Create;
    owned := true;
  end
  else
    owned := false;
  try
    if TrySOInvoke(ctx, Obj, method, Params, Result) <> irSuccess then
      raise Exception.Create('Invalid method call');
  finally
    if owned then
      ctx.free;
  end;
end;

function SOInvoke(const Obj: Tvalue; const method: string; const Params: string; ctx: TSuperRttiContext): ISuperObject; overload;
begin
  Result := SOInvoke(Obj, method, SO(Params), ctx)
end;

function TrySOInvoke(var ctx: TSuperRttiContext; const Obj: Tvalue; const method: string; const Params: ISuperObject; var Return: ISuperObject)
  : TSuperInvokeResult;
var
  T: TRttiInstanceType;
  M: TRttiMethod;
  A: TArray<Tvalue>;
  ps: TArray<TRttiParameter>;
  v: Tvalue;
  index: ISuperObject;

  function GetParams: Boolean;
  var
    I: Integer;
  begin
    case ObjectGetType(Params) of
      stArray:
        for I := 0 to Length(ps) - 1 do
          if (pfOut in ps[I].Flags) then
            Tvalue.Make(nil, ps[I].ParamType.Handle, A[I])
          else if not ctx.FromJson(ps[I].ParamType.Handle, Params.AsArray[I], A[I]) then
            Exit(false);
      stObject:
        for I := 0 to Length(ps) - 1 do
          if (pfOut in ps[I].Flags) then
            Tvalue.Make(nil, ps[I].ParamType.Handle, A[I])
          else if not ctx.FromJson(ps[I].ParamType.Handle, Params.AsObject[ps[I].name], A[I]) then
            Exit(false);
      stNull:
        ;
    else
      Exit(false);
    end;
    Result := true;
  end;

  procedure SetParams;
  var
    I: Integer;
  begin
    case ObjectGetType(Params) of
      stArray:
        for I := 0 to Length(ps) - 1 do
          if (ps[I].Flags * [pfVar, pfOut]) <> [] then
            Params.AsArray[I] := ctx.ToJson(A[I], index);
      stObject:
        for I := 0 to Length(ps) - 1 do
          if (ps[I].Flags * [pfVar, pfOut]) <> [] then
            Params.AsObject[ps[I].name] := ctx.ToJson(A[I], index);
    end;
  end;

begin
  Result := irSuccess;
  index := SO;
  case Obj.Kind of
    tkClass:
      begin
        T := TRttiInstanceType(ctx.Context.GetType(Obj.AsObject.ClassType));
        M := T.GetMethod(method);
        if M = nil then
          Exit(irMethothodError);
        ps := M.GetParameters;
        SetLength(A, Length(ps));
        if not GetParams then
          Exit(irParamError);
        if M.IsClassMethod then
        begin
          v := M.Invoke(Obj.AsObject.ClassType, A);
          Return := ctx.ToJson(v, index);
          SetParams;
        end
        else
        begin
          v := M.Invoke(Obj, A);
          Return := ctx.ToJson(v, index);
          SetParams;
        end;
      end;
    tkClassRef:
      begin
        T := TRttiInstanceType(ctx.Context.GetType(Obj.AsClass));
        M := T.GetMethod(method);
        if M = nil then
          Exit(irMethothodError);
        ps := M.GetParameters;
        SetLength(A, Length(ps));

        if not GetParams then
          Exit(irParamError);
        if M.IsClassMethod then
        begin
          v := M.Invoke(Obj, A);
          Return := ctx.ToJson(v, index);
          SetParams;
        end
        else
          Exit(irError);
      end;
  else
    Exit(irError);
  end;
end;

{$ENDIF}
{ TSuperEnumerator }

constructor TSuperEnumerator.Create(const Obj: ISuperObject);
begin
  FObj := Obj;
  FCount := -1;
  if ObjectIsType(FObj, stObject) then
    FObjEnum := FObj.AsObject.GetEnumerator
  else
    FObjEnum := nil;
end;

destructor TSuperEnumerator.Destroy;
begin
  if FObjEnum <> nil then
    FObjEnum.free;
end;

function TSuperEnumerator.MoveNext: Boolean;
begin
  case ObjectGetType(FObj) of
    stObject:
      Result := FObjEnum.MoveNext;
    stArray:
      begin
        Inc(FCount);
        if FCount < FObj.AsArray.Length then
          Result := true
        else
          Result := false;
      end;
  else
    Result := false;
  end;
end;

function TSuperEnumerator.GetCurrent: ISuperObject;
begin
  case ObjectGetType(FObj) of
    stObject:
      Result := FObjEnum.Current.value;
    stArray:
      Result := FObj.AsArray.GetO(FCount);
  else
    Result := FObj;
  end;
end;

{ TSuperObject }

constructor TSuperObject.Create(jt: TSuperType);
begin
  inherited Create;
{$IFDEF DEBUG}
  InterlockedIncrement(debugcount);
{$ENDIF}
  FProcessing := false;
  FDataPtr := nil;
  FDataType := jt;
  case FDataType of
    stObject:
      FO.c_object := TSuperTableString.Create;
    stArray:
      FO.c_array := TSuperArray.Create;
    stString:
      FOString := '';
  else
    FO.c_object := nil;
  end;
end;

constructor TSuperObject.Create(B: Boolean);
begin
  Create(stBoolean);
  FO.c_Boolean := B;
end;

constructor TSuperObject.Create(I: SuperInt);
begin
  Create(stInt);
  FO.c_int := I;
end;

constructor TSuperObject.Create(D: Double);
begin
  Create(stDouble);
  FO.c_double := D;
end;

constructor TSuperObject.CreateCurrency(C: Currency);
begin
  Create(stCurrency);
  FO.c_currency := C;
end;

destructor TSuperObject.Destroy;
begin
{$IFDEF DEBUG}
  InterlockedDecrement(debugcount);
{$ENDIF}
  case FDataType of
    stObject:
      FO.c_object.free;
    stArray:
      FO.c_array.free;
  end;
  inherited;
end;

function TSuperObject.Write(writer: TSuperWriter; indent: Boolean; escape: Boolean; level: Integer): Integer;
  function DoEscape(str: PSOChar; len: Integer): Integer;
  var
    pos, start_offset: Integer;
    C: SOChar;
    buf: array [0 .. 5] of SOChar;
  type
    TByteChar = record
      case Integer of
        0:
          (A, B: byte);
        1:
          (C: WideChar);
    end;

  begin
    if str = nil then
    begin
      Result := 0;
      Exit;
    end;
    pos := 0;
    start_offset := 0;
    with writer do
      while pos < len do
      begin
        C := str[pos];
        case C of
          #8, #9, #10, #12, #13, '"', '\', '/':
            begin
              if (pos - start_offset > 0) then
                Append(str + start_offset, pos - start_offset);

              if (C = #8) then
                Append(ESC_BS, 2)
              else if (C = #9) then
                Append(ESC_TAB, 2)
              else if (C = #10) then
                Append(ESC_LF, 2)
              else if (C = #12) then
                Append(ESC_FF, 2)
              else if (C = #13) then
                Append(ESC_CR, 2)
              else if (C = '"') then
                Append(ESC_QUOT, 2)
              else if (C = '\') then
                Append(ESC_SL, 2)
              else if (C = '/') then
                Append(ESC_SR, 2);
              Inc(pos);
              start_offset := pos;
            end;
        else
          if (SOIChar(C) > 255) then
          begin
            if (pos - start_offset > 0) then
              Append(str + start_offset, pos - start_offset);
            buf[0] := '\';
            buf[1] := 'u';
            buf[2] := super_hex_chars[TByteChar(C).B shr 4];
            buf[3] := super_hex_chars[TByteChar(C).B and $F];
            buf[4] := super_hex_chars[TByteChar(C).A shr 4];
            buf[5] := super_hex_chars[TByteChar(C).A and $F];
            Append(@buf, 6);
            Inc(pos);
            start_offset := pos;
          end
          else if (C < #32) or (C > #127) then
          begin
            if (pos - start_offset > 0) then
              Append(str + start_offset, pos - start_offset);
            buf[0] := '\';
            buf[1] := 'u';
            buf[2] := '0';
            buf[3] := '0';
            buf[4] := super_hex_chars[Ord(C) shr 4];
            buf[5] := super_hex_chars[Ord(C) and $F];
            Append(buf, 6);
            Inc(pos);
            start_offset := pos;
          end
          else
            Inc(pos);
        end;
      end;
    if (pos - start_offset > 0) then
      writer.Append(str + start_offset, pos - start_offset);
    Result := 0;
  end;

  function DoMinimalEscape(str: PSOChar; len: Integer): Integer;
  var
    pos, start_offset: Integer;
    C: SOChar;
  type
    TByteChar = record
      case Integer of
        0:
          (A, B: byte);
        1:
          (C: WideChar);
    end;

  begin
    if str = nil then
    begin
      Result := 0;
      Exit;
    end;
    pos := 0;
    start_offset := 0;
    with writer do
      while pos < len do
      begin
        C := str[pos];
        case C of
          #0:
            begin
              if (pos - start_offset > 0) then
                Append(str + start_offset, pos - start_offset);
              Append(ESC_ZERO, 6);
              Inc(pos);
              start_offset := pos;
            end;
          '"':
            begin
              if (pos - start_offset > 0) then
                Append(str + start_offset, pos - start_offset);
              Append(ESC_QUOT, 2);
              Inc(pos);
              start_offset := pos;
            end;
          '\':
            begin
              if (pos - start_offset > 0) then
                Append(str + start_offset, pos - start_offset);
              Append(ESC_SL, 2);
              Inc(pos);
              start_offset := pos;
            end;
        else
          Inc(pos);
        end;
      end;
    if (pos - start_offset > 0) then
      writer.Append(str + start_offset, pos - start_offset);
    Result := 0;
  end;

  procedure _indent(I: shortint; r: Boolean);
  begin
    Inc(level, I);
    if r then
      with writer do
      begin
{$IFDEF MSWINDOWS}
        Append(TOK_CRLF, 2);
{$ELSE}
        Append(TOK_LF, 1);
{$ENDIF}
        for I := 0 to level - 1 do
          Append(TOK_SP, 1);
      end;
  end;

var
  k, j: Integer;
  iter: TSuperObjectIter;
  st: AnsiString;
  val: ISuperObject;
const
  ENDSTR_A: PSOChar = '": ';
  ENDSTR_B: PSOChar = '":';
begin

  if FProcessing then
  begin
    Result := writer.Append(TOK_NULL, 4);
    Exit;
  end;

  FProcessing := true;
  with writer do
    try
      case FDataType of
        stObject:
          if FO.c_object.FCount > 0 then
          begin
            k := 0;
            Append(TOK_CBL, 1);
            if indent then
              _indent(1, false);
            if ObjectFindFirst(Self, iter) then
              repeat
{$IFDEF SUPER_METHOD}
                if (iter.val = nil) or not ObjectIsType(iter.val, stMethod) then
                begin
{$ENDIF}
                  if (iter.val = nil) or (not iter.val.Processing) then
                  begin
                    if (k <> 0) then
                      Append(TOK_COM, 1);
                    if indent then
                      _indent(0, true);
                    Append(TOK_DQT, 1);
                    if escape then
                      DoEscape(PSOChar(iter.key), Length(iter.key))
                    else
                      DoMinimalEscape(PSOChar(iter.key), Length(iter.key));
                    if indent then
                      Append(ENDSTR_A, 3)
                    else
                      Append(ENDSTR_B, 2);
                    if (iter.val = nil) then
                      Append(TOK_NULL, 4)
                    else
                      iter.val.Write(writer, indent, escape, level);
                    Inc(k);
                  end;
{$IFDEF SUPER_METHOD}
                end;
{$ENDIF}
              until not ObjectFindNext(iter);
            ObjectFindClose(iter);
            if indent then
              _indent(-1, true);
            Result := Append(TOK_CBR, 1);
          end
          else
            Result := Append(TOK_OBJ, 2);
        stBoolean:
          begin
            if (FO.c_Boolean) then
              Result := Append(TOK_TRUE, 4)
            else
              Result := Append(TOK_FALSE, 5);
          end;
        stInt:
          begin
            str(FO.c_int, st);
            Result := Append(PSOChar(SOString(st)));
          end;
        stDouble:
          Result := Append(PSOChar(FloatToJson(FO.c_double)));
        stCurrency:
          begin
            Result := Append(PSOChar(CurrToJson(FO.c_currency)));
          end;
        stString:
          begin
            Append(TOK_DQT, 1);
            if escape then
              DoEscape(PSOChar(FOString), Length(FOString))
            else
              DoMinimalEscape(PSOChar(FOString), Length(FOString));
            Append(TOK_DQT, 1);
            Result := 0;
          end;
        stArray:
          if FO.c_array.FLength > 0 then
          begin
            Append(TOK_ARL, 1);
            if indent then
              _indent(1, true);
            k := 0;
            j := 0;
            while k < FO.c_array.FLength do
            begin

              val := FO.c_array.GetO(k);
{$IFDEF SUPER_METHOD}
              if not ObjectIsType(val, stMethod) then
              begin
{$ENDIF}
                if (val = nil) or (not val.Processing) then
                begin
                  if (j <> 0) then
                    Append(TOK_COM, 1);
                  if (val = nil) then
                    Append(TOK_NULL, 4)
                  else
                    val.Write(writer, indent, escape, level);
                  Inc(j);
                end;
{$IFDEF SUPER_METHOD}
              end;
{$ENDIF}
              Inc(k);
            end;
            if indent then
              _indent(-1, false);
            Result := Append(TOK_ARR, 1);
          end
          else
            Result := Append(TOK_ARRAY, 2);
        stNull:
          Result := Append(TOK_NULL, 4);
      else
        Result := 0;
      end;
    finally
      FProcessing := false;
    end;
end;

function TSuperObject.IsType(AType: TSuperType): Boolean;
begin
  Result := AType = FDataType;
end;

function TSuperObject.AsBoolean: Boolean;
begin
  case FDataType of
    stBoolean:
      Result := FO.c_Boolean;
    stInt:
      Result := (FO.c_int <> 0);
    stDouble:
      Result := (FO.c_double <> 0);
    stCurrency:
      Result := (FO.c_currency <> 0);
    stString:
      Result := (Length(FOString) <> 0);
    stNull:
      Result := false;
  else
    Result := true;
  end;
end;

function TSuperObject.AsInteger: SuperInt;
var
  code: Integer;
  cint: SuperInt;
begin
  case FDataType of
    stInt:
      Result := FO.c_int;
    stDouble:
      Result := round(FO.c_double);
    stCurrency:
      Result := round(FO.c_currency);
    stBoolean:
      Result := Ord(FO.c_Boolean);
    stString:
      begin
        val(FOString, cint, code);
        if code = 0 then
          Result := cint
        else
          Result := 0;
      end;
  else
    Result := 0;
  end;
end;

function TSuperObject.AsDouble: Double;
var
  code: Integer;
  cdouble: Double;
begin
  case FDataType of
    stDouble:
      Result := FO.c_double;
    stCurrency:
      Result := FO.c_currency;
    stInt:
      Result := FO.c_int;
    stBoolean:
      Result := Ord(FO.c_Boolean);
    stString:
      begin
        val(FOString, cdouble, code);
        if code = 0 then
          Result := cdouble
        else
          Result := 0.0;
      end;
  else
    Result := 0.0;
  end;
end;

function TSuperObject.AsCurrency: Currency;
var
  code: Integer;
  cdouble: Double;
begin
  case FDataType of
    stDouble:
      Result := FO.c_double;
    stCurrency:
      Result := FO.c_currency;
    stInt:
      Result := FO.c_int;
    stBoolean:
      Result := Ord(FO.c_Boolean);
    stString:
      begin
        val(FOString, cdouble, code);
        if code = 0 then
          Result := cdouble
        else
          Result := 0.0;
      end;
  else
    Result := 0.0;
  end;
end;

function TSuperObject.AsString: SOString;
begin
  case FDataType of
    stString:
      Result := FOString;
    stNull:
      Result := '';
  else
    Result := AsJSon(false, false);
  end;
end;

function TSuperObject.GetEnumerator: TSuperEnumerator;
begin
  Result := TSuperEnumerator.Create(Self);
end;

procedure TSuperObject.AfterConstruction;
begin
  InterlockedDecrement(FRefCount);
end;

procedure TSuperObject.BeforeDestruction;
begin
  if RefCount <> 0 then
    raise Exception.Create('Invalid pointer');
end;

function TSuperObject.AsArray: TSuperArray;
begin
  if FDataType = stArray then
    Result := FO.c_array
  else
    Result := nil;
end;

function TSuperObject.AsObject: TSuperTableString;
begin
  if FDataType = stObject then
    Result := FO.c_object
  else
    Result := nil;
end;

function TSuperObject.AsJSon(indent, escape: Boolean): SOString;
var
  pb: TSuperWriterString;
begin
  pb := TSuperWriterString.Create;
  try
    if (Write(pb, indent, escape, 0) < 0) then
    begin
      Result := '';
      Exit;
    end;
    if pb.FBPos > 0 then
      Result := pb.FBuf
    else
      Result := '';
  finally
    pb.free;
  end;
end;

class function TSuperObject.ParseString(S: PSOChar; strict: Boolean; partial: Boolean; const This: ISuperObject; options: TSuperFindOptions;
  const put: ISuperObject; dt: TSuperType): ISuperObject;
var
  tok: TSuperTokenizer;
  Obj: ISuperObject;
begin
  tok := TSuperTokenizer.Create;
  Obj := ParseEx(tok, S, -1, strict, This, options, put, dt);
  if (tok.err <> teSuccess) or (not partial and (S[tok.char_offset] <> #0)) then
    Result := nil
  else
    Result := Obj;
  tok.free;
end;

class function TSuperObject.ParseStream(stream: TStream; strict: Boolean; partial: Boolean; const This: ISuperObject; options: TSuperFindOptions;
  const put: ISuperObject; dt: TSuperType): ISuperObject;
const
  BUFFER_SIZE = 1024;
var
  tok: TSuperTokenizer;
  buffera: array [0 .. BUFFER_SIZE - 1] of AnsiChar;
  bufferw: array [0 .. BUFFER_SIZE - 1] of SOChar;
  bom: array [0 .. 1] of byte;
  unicode: Boolean;
  j, Size: Integer;
  st: string;
begin
  st := '';
  tok := TSuperTokenizer.Create;

  if (stream.Read(bom, sizeof(bom)) = 2) and (bom[0] = $FF) and (bom[1] = $FE) then
  begin
    unicode := true;
    Size := stream.Read(bufferw, BUFFER_SIZE * sizeof(SOChar)) div sizeof(SOChar);
  end
  else
  begin
    unicode := false;
    stream.Seek(0, soFromBeginning);
    Size := stream.Read(buffera, BUFFER_SIZE);
  end;

  while Size > 0 do
  begin
    if not unicode then
      for j := 0 to Size - 1 do
        bufferw[j] := SOChar(buffera[j]);
    ParseEx(tok, bufferw, Size, strict, This, options, put, dt);

    if tok.err = teContinue then
    begin
      if not unicode then
        Size := stream.Read(buffera, BUFFER_SIZE)
      else
        Size := stream.Read(bufferw, BUFFER_SIZE * sizeof(SOChar)) div sizeof(SOChar);
    end
    else
      Break;
  end;
  if (tok.err <> teSuccess) or (not partial and (st[tok.char_offset] <> #0)) then
    Result := nil
  else
    Result := tok.stack[tok.depth].Current;
  tok.free;
end;

class function TSuperObject.ParseFile(const FileName: string; strict: Boolean; partial: Boolean; const This: ISuperObject; options: TSuperFindOptions;
  const put: ISuperObject; dt: TSuperType): ISuperObject;
var
  stream: TFileStream;
begin
  stream := TFileStream.Create(FileName, fmOpenRead, fmShareDenyWrite);
  try
    Result := ParseStream(stream, strict, partial, This, options, put, dt);
  finally
    stream.free;
  end;
end;

class function TSuperObject.ParseEx(tok: TSuperTokenizer; str: PSOChar; len: Integer; strict: Boolean; const This: ISuperObject;
  options: TSuperFindOptions; const put: ISuperObject; dt: TSuperType): ISuperObject;

const
  spaces = [#32, #8, #9, #10, #12, #13];
  delimiters = ['"', '.', '[', ']', '{', '}', '(', ')', ',', ':', #0];
  reserved = delimiters + spaces;
  path = ['a' .. 'z', 'A' .. 'Z', '.', '_'];

  function hexdigit(x: SOChar): byte; {$IFDEF HAVE_INLINE} inline; {$ENDIF}
  begin
    if x <= '9' then
      Result := byte(x) - byte('0')
    else
      Result := (byte(x) and 7) + 9;
  end;
  function min(v1, v2: Integer): Integer; {$IFDEF HAVE_INLINE} inline; {$ENDIF}
  begin
    if v1 < v2 then
      Result := v1
    else
      Result := v2
  end;

var
  Obj: ISuperObject;
  v: SOChar;
{$IFDEF SUPER_METHOD}
  sm: TSuperMethod;
{$ENDIF}
  numi: SuperInt;
  numd: Double;
  code: Integer;
  TokRec: PSuperTokenerSrec;
  evalstack: Integer;
  p: PSOChar;

  function IsEndDelimiter(v: AnsiChar): Boolean;
  begin
    if tok.depth > 0 then
      case tok.stack[tok.depth - 1].state of
        tsArrayAdd:
          Result := v in [',', ']', #0];
        tsObjectvalueAdd:
          Result := v in [',', '}', #0];
      else
        Result := v = #0;
      end
    else
      Result := v = #0;
  end;

label out , redo_char;
begin
  evalstack := 0;
  Obj := nil;
  Result := nil;
  TokRec := @tok.stack[tok.depth];

  tok.char_offset := 0;
  tok.err := teSuccess;

  repeat
    if (tok.char_offset = len) then
    begin
      if (tok.depth = 0) and (TokRec^.state = tsEatws) and (TokRec^.saved_state = tsFinish) then
        tok.err := teSuccess
      else
        tok.err := teContinue;
      goto out;
    end;

    v := str^;

    case v of
      #10:
        begin
          Inc(tok.line);
          tok.col := 0;
        end;
      #9:
        Inc(tok.col, 4);
    else
      Inc(tok.col);
    end;

  redo_char:
    case TokRec^.state of
      tsEatws:
        begin
          if (SOIChar(v) < 256) and (AnsiChar(v) in spaces) then { nop }
          else if (v = '/') then
          begin
            tok.pb.Reset;
            tok.pb.Append(@v, 1);
            TokRec^.state := tsCommentStart;
          end
          else
          begin
            TokRec^.state := TokRec^.saved_state;
            goto redo_char;
          end
        end;

      tsStart:
        case v of
          '"', '''':
            begin
              TokRec^.state := tsString;
              tok.pb.Reset;
              tok.quote_char := v;
            end;
          '-':
            begin
              TokRec^.state := tsNumber;
              tok.pb.Reset;
              tok.is_double := 0;
              tok.floatcount := -1;
              goto redo_char;
            end;

          '0' .. '9':
            begin
              if (tok.depth = 0) then
                case ObjectGetType(This) of
                  stObject:
                    begin
                      TokRec^.state := tsIdentifier;
                      TokRec^.Current := This;
                      goto redo_char;
                    end;
                end;
              TokRec^.state := tsNumber;
              tok.pb.Reset;
              tok.is_double := 0;
              tok.floatcount := -1;
              goto redo_char;
            end;
          '{':
            begin
              TokRec^.state := tsEatws;
              TokRec^.saved_state := tsObjectFieldStart;
              TokRec^.Current := TSuperObject.Create(stObject);
            end;
          '[':
            begin
              TokRec^.state := tsEatws;
              TokRec^.saved_state := tsArray;
              TokRec^.Current := TSuperObject.Create(stArray);
            end;
{$IFDEF SUPER_METHOD}
          '(':
            begin
              if (tok.depth = 0) and ObjectIsType(This, stMethod) then
              begin
                TokRec^.Current := This;
                TokRec^.state := tsParamvalue;
              end;
            end;
{$ENDIF}
          'N', 'n':
            begin
              TokRec^.state := tsNull;
              tok.pb.Reset;
              tok.st_pos := 0;
              goto redo_char;
            end;
          'T', 't', 'F', 'f':
            begin
              TokRec^.state := tsBoolean;
              tok.pb.Reset;
              tok.st_pos := 0;
              goto redo_char;
            end;
        else
          TokRec^.state := tsIdentifier;
          tok.pb.Reset;
          goto redo_char;
        end;

      tsFinish:
        begin
          if (tok.depth = 0) then
            goto out;
          Obj := TokRec^.Current;
          tok.ResetLevel(tok.depth);
          dec(tok.depth);
          TokRec := @tok.stack[tok.depth];
          goto redo_char;
        end;

      tsNull:
        begin
          tok.pb.Append(@v, 1);
          if (StrLComp(TOK_NULL, PSOChar(tok.pb.FBuf), min(tok.st_pos + 1, 4)) = 0) then
          begin
            if (tok.st_pos = 4) then
              if (((SOIChar(v) < 256) and (AnsiChar(v) in path)) or (SOIChar(v) >= 256)) then
                TokRec^.state := tsIdentifier
              else
              begin
                TokRec^.Current := TSuperObject.Create(stNull);
                TokRec^.saved_state := tsFinish;
                TokRec^.state := tsEatws;
                goto redo_char;
              end;
          end
          else
          begin
            TokRec^.state := tsIdentifier;
            tok.pb.FBuf[tok.st_pos] := #0;
            dec(tok.pb.FBPos);
            goto redo_char;
          end;
          Inc(tok.st_pos);
        end;

      tsCommentStart:
        begin
          if (v = '*') then
          begin
            TokRec^.state := tsComment;
          end
          else if (v = '/') then
          begin
            TokRec^.state := tsCommentEol;
          end
          else
          begin
            tok.err := teParseComment;
            goto out;
          end;
          tok.pb.Append(@v, 1);
        end;

      tsComment:
        begin
          if (v = '*') then
            TokRec^.state := tsCommentEnd;
          tok.pb.Append(@v, 1);
        end;

      tsCommentEol:
        begin
          if (v = #10) then
            TokRec^.state := tsEatws
          else
            tok.pb.Append(@v, 1);
        end;

      tsCommentEnd:
        begin
          tok.pb.Append(@v, 1);
          if (v = '/') then
            TokRec^.state := tsEatws
          else
            TokRec^.state := tsComment;
        end;

      tsString:
        begin
          if (v = tok.quote_char) then
          begin
            TokRec^.Current := TSuperObject.Create(SOString(tok.pb.GetString));
            TokRec^.saved_state := tsFinish;
            TokRec^.state := tsEatws;
          end
          else if (v = '\') then
          begin
            TokRec^.saved_state := tsString;
            TokRec^.state := tsStringEscape;
          end
          else
          begin
            tok.pb.Append(@v, 1);
          end
        end;

      tsEvalProperty:
        begin
          if (TokRec^.Current = nil) and (foCreatePath in options) then
          begin
            TokRec^.Current := TSuperObject.Create(stObject);
            TokRec^.parent.AsObject.PutO(tok.pb.FBuf, TokRec^.Current)
          end
          else if not ObjectIsType(TokRec^.Current, stObject) then
          begin
            tok.err := teEvalObject;
            goto out;
          end;
          tok.pb.Reset;
          TokRec^.state := tsIdentifier;
          goto redo_char;
        end;

      tsEvalArray:
        begin
          if (TokRec^.Current = nil) and (foCreatePath in options) then
          begin
            TokRec^.Current := TSuperObject.Create(stArray);
            TokRec^.parent.AsObject.PutO(tok.pb.FBuf, TokRec^.Current)
          end
          else if not ObjectIsType(TokRec^.Current, stArray) then
          begin
            tok.err := teEvalArray;
            goto out;
          end;
          tok.pb.Reset;
          TokRec^.state := tsParamvalue;
          goto redo_char;
        end;
{$IFDEF SUPER_METHOD}
      tsEvalMethod:
        begin
          if ObjectIsType(TokRec^.Current, stMethod) and Assigned(TokRec^.Current.AsMethod) then
          begin
            tok.pb.Reset;
            TokRec^.Obj := TSuperObject.Create(stArray);
            TokRec^.state := tsMethodvalue;
            goto redo_char;
          end
          else
          begin
            tok.err := teEvalMethod;
            goto out;
          end;
        end;

      tsMethodvalue:
        begin
          case v of
            ')':
              TokRec^.state := tsIdentifier;
          else
            if (tok.depth >= SUPER_TOKENER_MAX_DEPTH - 1) then
            begin
              tok.err := teDepth;
              goto out;
            end;
            Inc(evalstack);
            TokRec^.state := tsMethodPut;
            Inc(tok.depth);
            tok.ResetLevel(tok.depth);
            TokRec := @tok.stack[tok.depth];
            goto redo_char;
          end;
        end;

      tsMethodPut:
        begin
          TokRec^.Obj.AsArray.Add(Obj);
          case v of
            ',':
              begin
                tok.pb.Reset;
                TokRec^.saved_state := tsMethodvalue;
                TokRec^.state := tsEatws;
              end;
            ')':
              begin
                if TokRec^.Obj.AsArray.Length = 1 then
                  TokRec^.Obj := TokRec^.Obj.AsArray.GetO(0);
                dec(evalstack);
                tok.pb.Reset;
                TokRec^.saved_state := tsIdentifier;
                TokRec^.state := tsEatws;
              end;
          else
            tok.err := teEvalMethod;
            goto out;
          end;
        end;
{$ENDIF}
      tsParamvalue:
        begin
          case v of
            ']':
              TokRec^.state := tsIdentifier;
          else
            if (tok.depth >= SUPER_TOKENER_MAX_DEPTH - 1) then
            begin
              tok.err := teDepth;
              goto out;
            end;
            Inc(evalstack);
            TokRec^.state := tsParamPut;
            Inc(tok.depth);
            tok.ResetLevel(tok.depth);
            TokRec := @tok.stack[tok.depth];
            goto redo_char;
          end;
        end;

      tsParamPut:
        begin
          dec(evalstack);
          TokRec^.Obj := Obj;
          tok.pb.Reset;
          TokRec^.saved_state := tsIdentifier;
          TokRec^.state := tsEatws;
          if v <> ']' then
          begin
            tok.err := teEvalArray;
            goto out;
          end;
        end;

      tsIdentifier:
        begin
          if (This = nil) then
          begin
            if (SOIChar(v) < 256) and IsEndDelimiter(AnsiChar(v)) then
            begin
              if not strict then
              begin
                tok.pb.TrimRight;
                TokRec^.Current := TSuperObject.Create(tok.pb.FBuf);
                TokRec^.saved_state := tsFinish;
                TokRec^.state := tsEatws;
                goto redo_char;
              end
              else
              begin
                tok.err := teParseString;
                goto out;
              end;
            end
            else if (v = '\') then
            begin
              TokRec^.saved_state := tsIdentifier;
              TokRec^.state := tsStringEscape;
            end
            else
              tok.pb.Append(@v, 1);
          end
          else
          begin
            if (SOIChar(v) < 256) and (AnsiChar(v) in reserved) then
            begin
              TokRec^.gparent := TokRec^.parent;
              if TokRec^.Current = nil then
                TokRec^.parent := This
              else
                TokRec^.parent := TokRec^.Current;

              case ObjectGetType(TokRec^.parent) of
                stObject:
                  case v of
                    '.':
                      begin
                        TokRec^.state := tsEvalProperty;
                        if tok.pb.FBPos > 0 then
                          TokRec^.Current := TokRec^.parent.AsObject.GetO(tok.pb.FBuf);
                      end;
                    '[':
                      begin
                        TokRec^.state := tsEvalArray;
                        if tok.pb.FBPos > 0 then
                          TokRec^.Current := TokRec^.parent.AsObject.GetO(tok.pb.FBuf);
                      end;
                    '(':
                      begin
                        TokRec^.state := tsEvalMethod;
                        if tok.pb.FBPos > 0 then
                          TokRec^.Current := TokRec^.parent.AsObject.GetO(tok.pb.FBuf);
                      end;
                  else
                    if tok.pb.FBPos > 0 then
                      TokRec^.Current := TokRec^.parent.AsObject.GetO(tok.pb.FBuf);
                    if (foPutvalue in options) and (evalstack = 0) then
                    begin
                      TokRec^.parent.AsObject.PutO(tok.pb.FBuf, put);
                      TokRec^.Current := put
                    end
                    else if (foDelete in options) and (evalstack = 0) then
                    begin
                      TokRec^.Current := TokRec^.parent.AsObject.Delete(tok.pb.FBuf);
                    end
                    else if (TokRec^.Current = nil) and (foCreatePath in options) then
                    begin
                      TokRec^.Current := TSuperObject.Create(dt);
                      TokRec^.parent.AsObject.PutO(tok.pb.FBuf, TokRec^.Current);
                    end;
                    if not(foDelete in options) then
                      TokRec^.Current := TokRec^.parent.AsObject.GetO(tok.pb.FBuf);
                    TokRec^.state := tsFinish;
                    goto redo_char;
                  end;
                stArray:
                  begin
                    if TokRec^.Obj <> nil then
                    begin
                      if not ObjectIsType(TokRec^.Obj, stInt) or (TokRec^.Obj.AsInteger < 0) then
                      begin
                        tok.err := teEvalInt;
                        TokRec^.Obj := nil;
                        goto out;
                      end;
                      numi := TokRec^.Obj.AsInteger;
                      TokRec^.Obj := nil;

                      TokRec^.Current := TokRec^.parent.AsArray.GetO(numi);
                      case v of
                        '.':
                          if (TokRec^.Current = nil) and (foCreatePath in options) then
                          begin
                            TokRec^.Current := TSuperObject.Create(stObject);
                            TokRec^.parent.AsArray.PutO(numi, TokRec^.Current);
                          end
                          else if (TokRec^.Current = nil) then
                          begin
                            tok.err := teEvalObject;
                            goto out;
                          end;
                        '[':
                          begin
                            if (TokRec^.Current = nil) and (foCreatePath in options) then
                            begin
                              TokRec^.Current := TSuperObject.Create(stArray);
                              TokRec^.parent.AsArray.Add(TokRec^.Current);
                            end
                            else if (TokRec^.Current = nil) then
                            begin
                              tok.err := teEvalArray;
                              goto out;
                            end;
                            TokRec^.state := tsEvalArray;
                          end;
                        '(':
                          TokRec^.state := tsEvalMethod;
                      else
                        if (foPutvalue in options) and (evalstack = 0) then
                        begin
                          TokRec^.parent.AsArray.PutO(numi, put);
                          TokRec^.Current := put;
                        end
                        else if (foDelete in options) and (evalstack = 0) then
                        begin
                          TokRec^.Current := TokRec^.parent.AsArray.Delete(numi);
                        end
                        else
                          TokRec^.Current := TokRec^.parent.AsArray.GetO(numi);
                        TokRec^.state := tsFinish;
                        goto redo_char
                      end;
                    end
                    else
                    begin
                      case v of
                        '.':
                          begin
                            if (foPutvalue in options) then
                            begin
                              TokRec^.Current := TSuperObject.Create(stObject);
                              TokRec^.parent.AsArray.Add(TokRec^.Current);
                            end
                            else
                              TokRec^.Current := TokRec^.parent.AsArray.GetO(TokRec^.parent.AsArray.FLength - 1);
                          end;
                        '[':
                          begin
                            if (foPutvalue in options) then
                            begin
                              TokRec^.Current := TSuperObject.Create(stArray);
                              TokRec^.parent.AsArray.Add(TokRec^.Current);
                            end
                            else
                              TokRec^.Current := TokRec^.parent.AsArray.GetO(TokRec^.parent.AsArray.FLength - 1);
                            TokRec^.state := tsEvalArray;
                          end;
                        '(':
                          begin
                            if not(foPutvalue in options) then
                              TokRec^.Current := TokRec^.parent.AsArray.GetO(TokRec^.parent.AsArray.FLength - 1)
                            else
                              TokRec^.Current := nil;

                            TokRec^.state := tsEvalMethod;
                          end;
                      else
                        if (foPutvalue in options) and (evalstack = 0) then
                        begin
                          TokRec^.parent.AsArray.Add(put);
                          TokRec^.Current := put;
                        end
                        else if tok.pb.FBPos = 0 then
                          TokRec^.Current := TokRec^.parent.AsArray.GetO(TokRec^.parent.AsArray.FLength - 1);
                        TokRec^.state := tsFinish;
                        goto redo_char
                      end;
                    end;
                  end;
{$IFDEF SUPER_METHOD}
                stMethod:
                  case v of
                    '.':
                      begin
                        TokRec^.Current := nil;
                        sm := TokRec^.parent.AsMethod;
                        sm(TokRec^.gparent, TokRec^.Obj, TokRec^.Current);
                        TokRec^.Obj := nil;
                      end;
                    '[':
                      begin
                        TokRec^.Current := nil;
                        sm := TokRec^.parent.AsMethod;
                        sm(TokRec^.gparent, TokRec^.Obj, TokRec^.Current);
                        TokRec^.state := tsEvalArray;
                        TokRec^.Obj := nil;
                      end;
                    '(':
                      begin
                        TokRec^.Current := nil;
                        sm := TokRec^.parent.AsMethod;
                        sm(TokRec^.gparent, TokRec^.Obj, TokRec^.Current);
                        TokRec^.state := tsEvalMethod;
                        TokRec^.Obj := nil;
                      end;
                  else
                    if not(foPutvalue in options) or (evalstack > 0) then
                    begin
                      TokRec^.Current := nil;
                      sm := TokRec^.parent.AsMethod;
                      sm(TokRec^.gparent, TokRec^.Obj, TokRec^.Current);
                      TokRec^.Obj := nil;
                      TokRec^.state := tsFinish;
                      goto redo_char
                    end
                    else
                    begin
                      tok.err := teEvalMethod;
                      TokRec^.Obj := nil;
                      goto out;
                    end;
                  end;
{$ENDIF}
              end;
            end
            else
              tok.pb.Append(@v, 1);
          end;
        end;

      tsStringEscape:
        case v of
          'b', 'n', 'r', 't', 'f':
            begin
              if (v = 'b') then
                tok.pb.Append(TOK_BS, 1)
              else if (v = 'n') then
                tok.pb.Append(TOK_LF, 1)
              else if (v = 'r') then
                tok.pb.Append(TOK_CR, 1)
              else if (v = 't') then
                tok.pb.Append(TOK_TAB, 1)
              else if (v = 'f') then
                tok.pb.Append(TOK_FF, 1);
              TokRec^.state := TokRec^.saved_state;
            end;
          'u':
            begin
              tok.ucs_char := 0;
              tok.st_pos := 0;
              TokRec^.state := tsEscapeUnicode;
            end;
          'x':
            begin
              tok.ucs_char := 0;
              tok.st_pos := 0;
              TokRec^.state := tsEscapeHexadecimal;
            end
        else
          tok.pb.Append(@v, 1);
          TokRec^.state := TokRec^.saved_state;
        end;

      tsEscapeUnicode:
        begin
          if ((SOIChar(v) < 256) and (AnsiChar(v) in super_hex_chars_set)) then
          begin
            Inc(tok.ucs_char, (Word(hexdigit(v)) shl ((3 - tok.st_pos) * 4)));
            Inc(tok.st_pos);
            if (tok.st_pos = 4) then
            begin
              tok.pb.Append(@tok.ucs_char, 1);
              TokRec^.state := TokRec^.saved_state;
            end
          end
          else
          begin
            tok.err := teParseString;
            goto out;
          end
        end;
      tsEscapeHexadecimal:
        begin
          if ((SOIChar(v) < 256) and (AnsiChar(v) in super_hex_chars_set)) then
          begin
            Inc(tok.ucs_char, (Word(hexdigit(v)) shl ((1 - tok.st_pos) * 4)));
            Inc(tok.st_pos);
            if (tok.st_pos = 2) then
            begin
              tok.pb.Append(@tok.ucs_char, 1);
              TokRec^.state := TokRec^.saved_state;
            end
          end
          else
          begin
            tok.err := teParseString;
            goto out;
          end
        end;
      tsBoolean:
        begin
          tok.pb.Append(@v, 1);
          if (StrLComp('true', PSOChar(tok.pb.FBuf), min(tok.st_pos + 1, 4)) = 0) then
          begin
            if (tok.st_pos = 4) then
              if (((SOIChar(v) < 256) and (AnsiChar(v) in path)) or (SOIChar(v) >= 256)) then
                TokRec^.state := tsIdentifier
              else
              begin
                TokRec^.Current := TSuperObject.Create(true);
                TokRec^.saved_state := tsFinish;
                TokRec^.state := tsEatws;
                goto redo_char;
              end
          end
          else if (StrLComp('false', PSOChar(tok.pb.FBuf), min(tok.st_pos + 1, 5)) = 0) then
          begin
            if (tok.st_pos = 5) then
              if (((SOIChar(v) < 256) and (AnsiChar(v) in path)) or (SOIChar(v) >= 256)) then
                TokRec^.state := tsIdentifier
              else
              begin
                TokRec^.Current := TSuperObject.Create(false);
                TokRec^.saved_state := tsFinish;
                TokRec^.state := tsEatws;
                goto redo_char;
              end
          end
          else
          begin
            TokRec^.state := tsIdentifier;
            tok.pb.FBuf[tok.st_pos] := #0;
            dec(tok.pb.FBPos);
            goto redo_char;
          end;
          Inc(tok.st_pos);
        end;

      tsNumber:
        begin
          if (SOIChar(v) < 256) and (AnsiChar(v) in super_number_chars_set) then
          begin
            tok.pb.Append(@v, 1);
            if (SOIChar(v) < 256) then
              case v of
                '.':
                  begin
                    tok.is_double := 1;
                    tok.floatcount := 0;
                  end;
                'e', 'E':
                  begin
                    tok.is_double := 1;
                    tok.floatcount := -1;
                  end;
                '0' .. '9':
                  begin

                    if (tok.is_double = 1) and (tok.floatcount >= 0) then
                    begin
                      Inc(tok.floatcount);
                      if tok.floatcount > 4 then
                        tok.floatcount := -1;
                    end;
                  end;
              end;
          end
          else
          begin
            if (tok.is_double = 0) then
            begin
              val(tok.pb.FBuf, numi, code);
              if ObjectIsType(This, stArray) then
              begin
                if (foPutvalue in options) and (evalstack = 0) then
                begin
                  This.AsArray.PutO(numi, put);
                  TokRec^.Current := put;
                end
                else if (foDelete in options) and (evalstack = 0) then
                  TokRec^.Current := This.AsArray.Delete(numi)
                else
                  TokRec^.Current := This.AsArray.GetO(numi);
              end
              else
                TokRec^.Current := TSuperObject.Create(numi);

            end
            else if (tok.is_double <> 0) then
            begin
              if tok.floatcount >= 0 then
              begin
                p := tok.pb.FBuf;
                while p^ <> '.' do
                  Inc(p);
                for code := 0 to tok.floatcount - 1 do
                begin
                  p^ := p[1];
                  Inc(p);
                end;
                p^ := #0;
                val(tok.pb.FBuf, numi, code);
                case tok.floatcount of
                  0:
                    numi := numi * 10000;
                  1:
                    numi := numi * 1000;
                  2:
                    numi := numi * 100;
                  3:
                    numi := numi * 10;
                end;
                TokRec^.Current := TSuperObject.CreateCurrency(PCurrency(@numi)^);
              end
              else
              begin
                val(tok.pb.FBuf, numd, code);
                TokRec^.Current := TSuperObject.Create(numd);
              end;
            end
            else
            begin
              tok.err := teParseNumber;
              goto out;
            end;
            TokRec^.saved_state := tsFinish;
            TokRec^.state := tsEatws;
            goto redo_char;
          end
        end;

      tsArray:
        begin
          if (v = ']') then
          begin
            TokRec^.saved_state := tsFinish;
            TokRec^.state := tsEatws;
          end
          else
          begin
            if (tok.depth >= SUPER_TOKENER_MAX_DEPTH - 1) then
            begin
              tok.err := teDepth;
              goto out;
            end;
            TokRec^.state := tsArrayAdd;
            Inc(tok.depth);
            tok.ResetLevel(tok.depth);
            TokRec := @tok.stack[tok.depth];
            goto redo_char;
          end
        end;

      tsArrayAdd:
        begin
          TokRec^.Current.AsArray.Add(Obj);
          TokRec^.saved_state := tsArraySep;
          TokRec^.state := tsEatws;
          goto redo_char;
        end;

      tsArraySep:
        begin
          if (v = ']') then
          begin
            TokRec^.saved_state := tsFinish;
            TokRec^.state := tsEatws;
          end
          else if (v = ',') then
          begin
            TokRec^.saved_state := tsArray;
            TokRec^.state := tsEatws;
          end
          else
          begin
            tok.err := teParseArray;
            goto out;
          end
        end;

      tsObjectFieldStart:
        begin
          if (v = '}') then
          begin
            TokRec^.saved_state := tsFinish;
            TokRec^.state := tsEatws;
          end
          else if (SOIChar(v) < 256) and (AnsiChar(v) in ['"', '''']) then
          begin
            tok.quote_char := v;
            tok.pb.Reset;
            TokRec^.state := tsObjectField;
          end
          else if not((SOIChar(v) < 256) and ((AnsiChar(v) in reserved) or strict)) then
          begin
            TokRec^.state := tsObjectUnquotedField;
            tok.pb.Reset;
            goto redo_char;
          end
          else
          begin
            tok.err := teParseObjectKeyName;
            goto out;
          end
        end;

      tsObjectField:
        begin
          if (v = tok.quote_char) then
          begin
            TokRec^.field_name := tok.pb.FBuf;
            TokRec^.saved_state := tsObjectFieldEnd;
            TokRec^.state := tsEatws;
          end
          else if (v = '\') then
          begin
            TokRec^.saved_state := tsObjectField;
            TokRec^.state := tsStringEscape;
          end
          else
          begin
            tok.pb.Append(@v, 1);
          end
        end;

      tsObjectUnquotedField:
        begin
          if (SOIChar(v) < 256) and (AnsiChar(v) in [':', #0]) then
          begin
            TokRec^.field_name := tok.pb.FBuf;
            TokRec^.saved_state := tsObjectFieldEnd;
            TokRec^.state := tsEatws;
            goto redo_char;
          end
          else if (v = '\') then
          begin
            TokRec^.saved_state := tsObjectUnquotedField;
            TokRec^.state := tsStringEscape;
          end
          else
            tok.pb.Append(@v, 1);
        end;

      tsObjectFieldEnd:
        begin
          if (v = ':') then
          begin
            TokRec^.saved_state := tsObjectvalue;
            TokRec^.state := tsEatws;
          end
          else
          begin
            tok.err := teParseObjectKeySep;
            goto out;
          end
        end;

      tsObjectvalue:
        begin
          if (tok.depth >= SUPER_TOKENER_MAX_DEPTH - 1) then
          begin
            tok.err := teDepth;
            goto out;
          end;
          TokRec^.state := tsObjectvalueAdd;
          Inc(tok.depth);
          tok.ResetLevel(tok.depth);
          TokRec := @tok.stack[tok.depth];
          goto redo_char;
        end;

      tsObjectvalueAdd:
        begin
          TokRec^.Current.AsObject.PutO(TokRec^.field_name, Obj);
          TokRec^.field_name := '';
          TokRec^.saved_state := tsObjectSep;
          TokRec^.state := tsEatws;
          goto redo_char;
        end;

      tsObjectSep:
        begin
          if (v = '}') then
          begin
            TokRec^.saved_state := tsFinish;
            TokRec^.state := tsEatws;
          end
          else if (v = ',') then
          begin
            TokRec^.saved_state := tsObjectFieldStart;
            TokRec^.state := tsEatws;
          end
          else
          begin
            tok.err := teParseObjectvalueSep;
            goto out;
          end
        end;
    end;
    Inc(str);
    Inc(tok.char_offset);
  until v = #0;

  if (TokRec^.state <> tsFinish) and (TokRec^.saved_state <> tsFinish) then
    tok.err := teParseEof;

out :
  if (tok.err in [teSuccess]) then
  begin
{$IFDEF SUPER_METHOD}
    if (foCallMethod in options) and ObjectIsType(TokRec^.Current, stMethod) and Assigned(TokRec^.Current.AsMethod) then
    begin
      sm := TokRec^.Current.AsMethod;
      sm(TokRec^.parent, put, Result);
    end
    else
{$ENDIF}
      Result := TokRec^.Current;
  end
  else
    Result := nil;
end;

procedure TSuperObject.PutO(const path: SOString; const value: ISuperObject);
begin
  ParseString(PSOChar(path), true, false, Self, [foCreatePath, foPutvalue], value);
end;

procedure TSuperObject.PutB(const path: SOString; value: Boolean);
begin
  ParseString(PSOChar(path), true, false, Self, [foCreatePath, foPutvalue], TSuperObject.Create(value));
end;

procedure TSuperObject.PutD(const path: SOString; value: Double);
begin
  ParseString(PSOChar(path), true, false, Self, [foCreatePath, foPutvalue], TSuperObject.Create(value));
end;

procedure TSuperObject.PutC(const path: SOString; value: Currency);
begin
  ParseString(PSOChar(path), true, false, Self, [foCreatePath, foPutvalue], TSuperObject.CreateCurrency(value));
end;

procedure TSuperObject.PutI(const path: SOString; value: SuperInt);
begin
  ParseString(PSOChar(path), true, false, Self, [foCreatePath, foPutvalue], TSuperObject.Create(value));
end;

procedure TSuperObject.PutS(const path: SOString; const value: SOString);
begin
  ParseString(PSOChar(path), true, false, Self, [foCreatePath, foPutvalue], TSuperObject.Create(value));
end;

{$IFDEF FPC}

function TSuperObject.QueryInterface({$IFDEF FPC_HAS_CONSTREF}constref{$ELSE}const {$ENDIF} iid: tguid; out Obj): LongInt; {$IFNDEF WINDOWS}cdecl{$ELSE}stdcall{$ENDIF};
{$ELSE}

function TSuperObject.QueryInterface(const iid: tguid; out Obj): HResult; stdcall;
{$ENDIF}
begin
  if GetInterface(iid, Obj) then
    Result := 0
  else
    Result := E_NOINTERFACE;
end;

function TSuperObject.SaveTo(stream: TStream; indent, escape: Boolean): Integer;
var
  pb: TSuperWriterStream;
begin
  if escape then
    pb := TSuperAnsiWriterStream.Create(stream)
  else
    pb := TSuperUnicodeWriterStream.Create(stream);

  if (Write(pb, indent, escape, 0) < 0) then
  begin
    pb.Reset;
    pb.free;
    Result := 0;
    Exit;
  end;
  Result := stream.Size;
  pb.free;
end;

function TSuperObject.CalcSize(indent, escape: Boolean): Integer;
var
  pb: TSuperWriterFake;
begin
  pb := TSuperWriterFake.Create;
  if (Write(pb, indent, escape, 0) < 0) then
  begin
    pb.free;
    Result := 0;
    Exit;
  end;
  Result := pb.FSize;
  pb.free;
end;

function TSuperObject.SaveTo(Socket: Integer; indent, escape: Boolean): Integer;
var
  pb: TSuperWriterSock;
begin
  pb := TSuperWriterSock.Create(Socket);
  if (Write(pb, indent, escape, 0) < 0) then
  begin
    pb.free;
    Result := 0;
    Exit;
  end;
  Result := pb.FSize;
  pb.free;
end;

constructor TSuperObject.Create(const S: SOString);
begin
  Create(stString);
  FOString := S;
end;

procedure TSuperObject.Clear(all: Boolean);
begin
  if FProcessing then
    Exit;
  FProcessing := true;
  try
    case FDataType of
      stBoolean:
        FO.c_Boolean := false;
      stDouble:
        FO.c_double := 0.0;
      stCurrency:
        FO.c_currency := 0.0;
      stInt:
        FO.c_int := 0;
      stObject:
        FO.c_object.Clear(all);
      stArray:
        FO.c_array.Clear(all);
      stString:
        FOString := '';
{$IFDEF SUPER_METHOD}
      stMethod:
        FO.c_method := nil;
{$ENDIF}
    end;
  finally
    FProcessing := false;
  end;
end;

procedure TSuperObject.Pack(all: Boolean = false);
begin
  if FProcessing then
    Exit;
  FProcessing := true;
  try
    case FDataType of
      stObject:
        FO.c_object.Pack(all);
      stArray:
        FO.c_array.Pack(all);
    end;
  finally
    FProcessing := false;
  end;
end;

function TSuperObject.GetN(const path: SOString): ISuperObject;
begin
  Result := ParseString(PSOChar(path), false, true, Self);
  if Result = nil then
    Result := TSuperObject.Create(stNull);
end;

procedure TSuperObject.PutN(const path: SOString; const value: ISuperObject);
begin
  if value = nil then
    ParseString(PSOChar(path), false, true, Self, [foCreatePath, foPutvalue], TSuperObject.Create(stNull))
  else
    ParseString(PSOChar(path), false, true, Self, [foCreatePath, foPutvalue], value);
end;

function TSuperObject.Delete(const path: SOString): ISuperObject;
begin
  Result := ParseString(PSOChar(path), false, true, Self, [foDelete]);
end;

function TSuperObject.Clone: ISuperObject;
var
  Ite: TSuperObjectIter;
  arr: TSuperArray;
  j: Integer;
begin
  case FDataType of
    stBoolean:
      Result := TSuperObject.Create(FO.c_Boolean);
    stDouble:
      Result := TSuperObject.Create(FO.c_double);
    stCurrency:
      Result := TSuperObject.CreateCurrency(FO.c_currency);
    stInt:
      Result := TSuperObject.Create(FO.c_int);
    stString:
      Result := TSuperObject.Create(FOString);
{$IFDEF SUPER_METHOD}
    stMethod:
      Result := TSuperObject.Create(FO.c_method);
{$ENDIF}
    stObject:
      begin
        Result := TSuperObject.Create(stObject);
        if ObjectFindFirst(Self, Ite) then
          with Result.AsObject do
            repeat
              PutO(Ite.key, Ite.val.Clone);
            until not ObjectFindNext(Ite);
        ObjectFindClose(Ite);
      end;
    stArray:
      begin
        Result := TSuperObject.Create(stArray);
        arr := AsArray;
        with Result.AsArray do
          for j := 0 to arr.Length - 1 do
            Add(arr.GetO(j).Clone);
      end;
    stNull:
      Result := TSuperObject.Create(stNull);
  else
    Result := nil;
  end;
end;

procedure TSuperObject.Merge(const Obj: ISuperObject; reference: Boolean);
var
  prop1, prop2: ISuperObject;
  Ite: TSuperObjectIter;
  arr: TSuperArray;
  j: Integer;
begin
  if ObjectIsType(Obj, FDataType) then
    case FDataType of
      stBoolean:
        FO.c_Boolean := Obj.AsBoolean;
      stDouble:
        FO.c_double := Obj.AsDouble;
      stCurrency:
        FO.c_currency := Obj.AsCurrency;
      stInt:
        FO.c_int := Obj.AsInteger;
      stString:
        FOString := Obj.AsString;
{$IFDEF SUPER_METHOD}
      stMethod:
        FO.c_method := Obj.AsMethod;
{$ENDIF}
      stObject:
        begin
          if ObjectFindFirst(Obj, Ite) then
            with FO.c_object do
              repeat
                prop1 := FO.c_object.GetO(Ite.key);
                if (prop1 <> nil) and (Ite.val <> nil) and (prop1.dataType = Ite.val.dataType) then
                  prop1.Merge(Ite.val)
                else if reference then
                  PutO(Ite.key, Ite.val)
                else if Ite.val <> nil then
                  PutO(Ite.key, Ite.val.Clone)
                else
                  PutO(Ite.key, nil)

                    until not ObjectFindNext(Ite);
                ObjectFindClose(Ite);
              end;
        stArray:
          begin
            arr := Obj.AsArray;
            with FO.c_array do
              for j := 0 to arr.Length - 1 do
              begin
                prop1 := GetO(j);
                prop2 := arr.GetO(j);
                if (prop1 <> nil) and (prop2 <> nil) and (prop1.dataType = prop2.dataType) then
                  prop1.Merge(prop2)
                else if reference then
                  PutO(j, prop2)
                else if prop2 <> nil then
                  PutO(j, prop2.Clone)
                else
                  PutO(j, nil);
              end;
          end;
        end;
    end;

  procedure TSuperObject.Merge(const str: SOString);
  begin
    Merge(TSuperObject.ParseString(PSOChar(str), false), true);
  end;

  class function TSuperObject.NewInstance: TObject;
  begin
    Result := inherited NewInstance;
    TSuperObject(Result).FRefCount := 1;
  end;

  function TSuperObject.ForcePath(const path: SOString; dataType: TSuperType = stObject): ISuperObject;
  begin
    Result := ParseString(PSOChar(path), false, true, Self, [foCreatePath], nil, dataType);
  end;

  function TSuperObject.Format(const str: SOString; BeginSep: SOChar; EndSep: SOChar): SOString;
  var
    P1, P2: PSOChar;
  begin
    Result := '';
    P2 := PSOChar(str);
    P1 := P2;
    while true do
      if P2^ = BeginSep then
      begin
        if P2 > P1 then
          Result := Result + Copy(P1, 0, P2 - P1);
        Inc(P2);
        P1 := P2;
        while true do
          if P2^ = EndSep then
            Break
          else if P2^ = #0 then
            Exit
          else
            Inc(P2);
        Result := Result + GetS(Copy(P1, 0, P2 - P1));
        Inc(P2);
        P1 := P2;
      end
      else if P2^ = #0 then
      begin
        if P2 > P1 then
          Result := Result + Copy(P1, 0, P2 - P1);
        Break;
      end
      else
        Inc(P2);
  end;

  function TSuperObject.GetO(const path: SOString): ISuperObject;
  begin
    Result := ParseString(PSOChar(path), false, true, Self);
  end;

  function TSuperObject.GetA(const path: SOString): TSuperArray;
  var
    Obj: ISuperObject;
  begin
    Obj := ParseString(PSOChar(path), false, true, Self);
    if Obj <> nil then
      Result := Obj.AsArray
    else
      Result := nil;
  end;

  function TSuperObject.GetB(const path: SOString): Boolean;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(path);
    if Obj <> nil then
      Result := Obj.AsBoolean
    else
      Result := false;
  end;

  function TSuperObject.GetD(const path: SOString): Double;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(path);
    if Obj <> nil then
      Result := Obj.AsDouble
    else
      Result := 0.0;
  end;

  function TSuperObject.GetC(const path: SOString): Currency;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(path);
    if Obj <> nil then
      Result := Obj.AsCurrency
    else
      Result := 0.0;
  end;

  function TSuperObject.GetI(const path: SOString): SuperInt;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(path);
    if Obj <> nil then
      Result := Obj.AsInteger
    else
      Result := 0;
  end;

  function TSuperObject.GetDataPtr: Pointer;
  begin
    Result := FDataPtr;
  end;

  function TSuperObject.GetDataType: TSuperType;
  begin
    Result := FDataType
  end;

  function TSuperObject.GetS(const path: SOString): SOString;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(path);
    if Obj <> nil then
      Result := Obj.AsString
    else
      Result := '';
  end;

  function TSuperObject.SaveTo(const FileName: string; indent, escape: Boolean): Integer;
  var
    stream: TFileStream;
  begin
    stream := TFileStream.Create(FileName, fmCreate);
    try
      Result := SaveTo(stream, indent, escape);
    finally
      stream.free;
    end;
  end;

  function TSuperObject.Validate(const rules: SOString; const defs: SOString = ''; callback: TSuperOnValidateError = nil;
    sender: Pointer = nil): Boolean;
  begin
    Result := Validate(TSuperObject.ParseString(PSOChar(rules), false), TSuperObject.ParseString(PSOChar(defs), false), callback, sender);
  end;

  function TSuperObject.Validate(const rules: ISuperObject; const defs: ISuperObject = nil; callback: TSuperOnValidateError = nil;
    sender: Pointer = nil): Boolean;
  type
    TDataType = (dtUnknown, dtStr, dtInt, dtFloat, dtNumber, dtText, dtBool, dtMap, dtSeq, dtScalar, dtAny);
  var
    datatypes: ISuperObject;
    names: ISuperObject;

    function FindInheritedProperty(const prop: PSOChar; p: ISuperObject): ISuperObject;
    var
      O: ISuperObject;
      e: TSuperAvlEntry;
    begin
      O := p[prop];
      if O <> nil then
        Result := O
      else
      begin
        O := p['inherit'];
        if (O <> nil) and ObjectIsType(O, stString) then
        begin
          e := names.AsObject.Search(O.AsString);
          if (e <> nil) then
            Result := FindInheritedProperty(prop, e.value)
          else
            Result := nil;
        end
        else
          Result := nil;
      end;
    end;

    function FindDataType(O: ISuperObject): TDataType;
    var
      e: TSuperAvlEntry;
      Obj: ISuperObject;
    begin
      Obj := FindInheritedProperty('type', O);
      if Obj <> nil then
      begin
        e := datatypes.AsObject.Search(Obj.AsString);
        if e <> nil then
          Result := TDataType(e.value.AsInteger)
        else
          Result := dtUnknown;
      end
      else
        Result := dtUnknown;
    end;

    procedure GetNames(O: ISuperObject);
    var
      Obj: ISuperObject;
      F: TSuperObjectIter;
    begin
      Obj := O['name'];
      if ObjectIsType(Obj, stString) then
        names[Obj.AsString] := O;

      case FindDataType(O) of
        dtMap:
          begin
            Obj := O['mapping'];
            if ObjectIsType(Obj, stObject) then
            begin
              if ObjectFindFirst(Obj, F) then
                repeat
                  if ObjectIsType(F.val, stObject) then
                    GetNames(F.val);
                until not ObjectFindNext(F);
              ObjectFindClose(F);
            end;
          end;
        dtSeq:
          begin
            Obj := O['sequence'];
            if ObjectIsType(Obj, stObject) then
              GetNames(Obj);
          end;
      end;
    end;

    function FindInheritedField(const prop: SOString; p: ISuperObject): ISuperObject;
    var
      O: ISuperObject;
      e: TSuperAvlEntry;
    begin
      O := p['mapping'];
      if ObjectIsType(O, stObject) then
      begin
        O := O.AsObject.GetO(prop);
        if O <> nil then
        begin
          Result := O;
          Exit;
        end;
      end;

      O := p['inherit'];
      if ObjectIsType(O, stString) then
      begin
        e := names.AsObject.Search(O.AsString);
        if (e <> nil) then
          Result := FindInheritedField(prop, e.value)
        else
          Result := nil;
      end
      else
        Result := nil;
    end;

    function InheritedFieldExist(const Obj: ISuperObject; p: ISuperObject; const name: SOString = ''): Boolean;
    var
      O: ISuperObject;
      e: TSuperAvlEntry;
      j: TSuperAvlIterator;
    begin
      Result := true;
      O := p['mapping'];
      if ObjectIsType(O, stObject) then
      begin
        j := TSuperAvlIterator.Create(O.AsObject);
        try
          j.First;
          e := j.GetIter;
          while e <> nil do
          begin
            if Obj.AsObject.Search(e.name) = nil then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veFieldNotFound, name + '.' + e.name);
            end;
            j.Next;
            e := j.GetIter;
          end;

        finally
          j.free;
        end;
      end;

      O := p['inherit'];
      if ObjectIsType(O, stString) then
      begin
        e := names.AsObject.Search(O.AsString);
        if (e <> nil) then
          Result := InheritedFieldExist(Obj, e.value, name) and Result;
      end;
    end;

    function getInheritedBool(F: PSOChar; p: ISuperObject; default: Boolean = false): Boolean;
    var
      O: ISuperObject;
    begin
      O := FindInheritedProperty(F, p);
      case ObjectGetType(O) of
        stBoolean:
          Result := O.AsBoolean;
        stNull:
          Result := Default;
      else
        Result := default;
        if Assigned(callback) then
          callback(sender, veRuleMalformated, F);
      end;
    end;

    procedure GetInheritedFieldList(list: ISuperObject; p: ISuperObject);
    var
      O: ISuperObject;
      e: TSuperAvlEntry;
      I: TSuperAvlIterator;
    begin
      Result := true;
      O := p['mapping'];
      if ObjectIsType(O, stObject) then
      begin
        I := TSuperAvlIterator.Create(O.AsObject);
        try
          I.First;
          e := I.GetIter;
          while e <> nil do
          begin
            if list.AsObject.Search(e.name) = nil then
              list[e.name] := e.value;
            I.Next;
            e := I.GetIter;
          end;

        finally
          I.free;
        end;
      end;

      O := p['inherit'];
      if ObjectIsType(O, stString) then
      begin
        e := names.AsObject.Search(O.AsString);
        if (e <> nil) then
          GetInheritedFieldList(list, e.value);
      end;
    end;

    function CheckEnum(O: ISuperObject; p: ISuperObject; name: SOString = ''): Boolean;
    var
      enum: ISuperObject;
      I: Integer;
    begin
      Result := false;
      enum := FindInheritedProperty('enum', p);
      case ObjectGetType(enum) of
        stArray:
          for I := 0 to enum.AsArray.Length - 1 do
            if (O.AsString = enum.AsArray[I].AsString) then
            begin
              Result := true;
              Exit;
            end;
        stNull:
          Result := true;
      else
        Result := false;
        if Assigned(callback) then
          callback(sender, veRuleMalformated, '');
        Exit;
      end;

      if (not Result) and Assigned(callback) then
        callback(sender, vevalueNotInEnum, name);
    end;

    function CheckLength(len: Integer; p: ISuperObject; const objpath: SOString): Boolean;
    var
      Length, O: ISuperObject;
    begin
      Result := true;
      Length := FindInheritedProperty('length', p);
      case ObjectGetType(Length) of
        stObject:
          begin
            O := Length.AsObject.GetO('min');
            if (O <> nil) and (O.AsInteger > len) then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veInvalidLength, objpath);
            end;
            O := Length.AsObject.GetO('max');
            if (O <> nil) and (O.AsInteger < len) then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veInvalidLength, objpath);
            end;
            O := Length.AsObject.GetO('minex');
            if (O <> nil) and (O.AsInteger >= len) then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veInvalidLength, objpath);
            end;
            O := Length.AsObject.GetO('maxex');
            if (O <> nil) and (O.AsInteger <= len) then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veInvalidLength, objpath);
            end;
          end;
        stNull:
          ;
      else
        Result := false;
        if Assigned(callback) then
          callback(sender, veRuleMalformated, '');
      end;
    end;

    function CheckRange(Obj: ISuperObject; p: ISuperObject; const objpath: SOString): Boolean;
    var
      Length, O: ISuperObject;
    begin
      Result := true;
      Length := FindInheritedProperty('range', p);
      case ObjectGetType(Length) of
        stObject:
          begin
            O := Length.AsObject.GetO('min');
            if (O <> nil) and (O.Compare(Obj) = cpGreat) then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veInvalidRange, objpath);
            end;
            O := Length.AsObject.GetO('max');
            if (O <> nil) and (O.Compare(Obj) = cpLess) then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veInvalidRange, objpath);
            end;
            O := Length.AsObject.GetO('minex');
            if (O <> nil) and (O.Compare(Obj) in [cpGreat, cpEqu]) then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veInvalidRange, objpath);
            end;
            O := Length.AsObject.GetO('maxex');
            if (O <> nil) and (O.Compare(Obj) in [cpLess, cpEqu]) then
            begin
              Result := false;
              if Assigned(callback) then
                callback(sender, veInvalidRange, objpath);
            end;
          end;
        stNull:
          ;
      else
        Result := false;
        if Assigned(callback) then
          callback(sender, veRuleMalformated, '');
      end;
    end;

    function process(O: ISuperObject; p: ISuperObject; objpath: SOString = ''): Boolean;
    var
      Ite: TSuperAvlIterator;
      ent: TSuperAvlEntry;
      P2, o2, sequence: ISuperObject;
      S: SOString;
      I: Integer;
      uniquelist, fieldlist: ISuperObject;
    begin
      Result := true;
      if (O = nil) then
      begin
        if getInheritedBool('required', p) then
        begin
          if Assigned(callback) then
            callback(sender, veFieldIsRequired, objpath);
          Result := false;
        end;
      end
      else
        case FindDataType(p) of
          dtStr:
            case ObjectGetType(O) of
              stString:
                begin
                  Result := Result and CheckLength(Length(O.AsString), p, objpath);
                  Result := Result and CheckRange(O, p, objpath);
                end;
            else
              if Assigned(callback) then
                callback(sender, veInvalidDataType, objpath);
              Result := false;
            end;
          dtBool:
            case ObjectGetType(O) of
              stBoolean:
                begin
                  Result := Result and CheckRange(O, p, objpath);
                end;
            else
              if Assigned(callback) then
                callback(sender, veInvalidDataType, objpath);
              Result := false;
            end;
          dtInt:
            case ObjectGetType(O) of
              stInt:
                begin
                  Result := Result and CheckRange(O, p, objpath);
                end;
            else
              if Assigned(callback) then
                callback(sender, veInvalidDataType, objpath);
              Result := false;
            end;
          dtFloat:
            case ObjectGetType(O) of
              stDouble, stCurrency:
                begin
                  Result := Result and CheckRange(O, p, objpath);
                end;
            else
              if Assigned(callback) then
                callback(sender, veInvalidDataType, objpath);
              Result := false;
            end;
          dtMap:
            case ObjectGetType(O) of
              stObject:
                begin
                  // all objects have and match a rule ?
                  Ite := TSuperAvlIterator.Create(O.AsObject);
                  try
                    Ite.First;
                    ent := Ite.GetIter;
                    while ent <> nil do
                    begin
                      P2 := FindInheritedField(ent.name, p);
                      if ObjectIsType(P2, stObject) then
                        Result := process(ent.value, P2, objpath + '.' + ent.name) and Result
                      else
                      begin
                        if Assigned(callback) then
                          callback(sender, veUnexpectedField, objpath + '.' + ent.name);
                        Result := false; // field have no rule
                      end;
                      Ite.Next;
                      ent := Ite.GetIter;
                    end;
                  finally
                    Ite.free;
                  end;

                  // all expected field exists ?
                  Result := InheritedFieldExist(O, p, objpath) and Result;
                end;
              stNull: { nop }
                ;
            else
              Result := false;
              if Assigned(callback) then
                callback(sender, veRuleMalformated, objpath);
            end;
          dtSeq:
            case ObjectGetType(O) of
              stArray:
                begin
                  sequence := FindInheritedProperty('sequence', p);
                  if sequence <> nil then
                    case ObjectGetType(sequence) of
                      stObject:
                        begin
                          for I := 0 to O.AsArray.Length - 1 do
                            Result := process(O.AsArray.GetO(I), sequence, objpath + '[' + IntToStr(I) + ']') and Result;
                          if getInheritedBool('unique', sequence) then
                          begin
                            // type is unique ?
                            uniquelist := TSuperObject.Create(stObject);
                            try
                              for I := 0 to O.AsArray.Length - 1 do
                              begin
                                S := O.AsArray.GetO(I).AsString;
                                if (S <> '') then
                                begin
                                  if uniquelist.AsObject.Search(S) = nil then
                                    uniquelist[S] := nil
                                  else
                                  begin
                                    Result := false;
                                    if Assigned(callback) then
                                      callback(sender, veDuplicateEntry, objpath + '[' + IntToStr(I) + ']');
                                  end;
                                end;
                              end;
                            finally
                              uniquelist := nil;
                            end;
                          end;

                          // field is unique ?
                          if (FindDataType(sequence) = dtMap) then
                          begin
                            fieldlist := TSuperObject.Create(stObject);
                            try
                              GetInheritedFieldList(fieldlist, sequence);
                              Ite := TSuperAvlIterator.Create(fieldlist.AsObject);
                              try
                                Ite.First;
                                ent := Ite.GetIter;
                                while ent <> nil do
                                begin
                                  if getInheritedBool('unique', ent.value) then
                                  begin
                                    uniquelist := TSuperObject.Create(stObject);
                                    try
                                      for I := 0 to O.AsArray.Length - 1 do
                                      begin
                                        o2 := O.AsArray.GetO(I);
                                        if o2 <> nil then
                                        begin
                                        S := o2.AsObject.GetO(ent.name).AsString;
                                        if (S <> '') then
                                        if uniquelist.AsObject.Search(S) = nil then
                                        uniquelist[S] := nil
                                        else
                                        begin
                                        Result := false;
                                        if Assigned(callback) then
                                        callback(sender, veDuplicateEntry, objpath + '[' + IntToStr(I) + '].' + ent.name);
                                        end;
                                        end;
                                      end;
                                    finally
                                      uniquelist := nil;
                                    end;
                                  end;
                                  Ite.Next;
                                  ent := Ite.GetIter;
                                end;
                              finally
                                Ite.free;
                              end;
                            finally
                              fieldlist := nil;
                            end;
                          end;

                        end;
                      stNull: { nop }
                        ;
                    else
                      Result := false;
                      if Assigned(callback) then
                        callback(sender, veRuleMalformated, objpath);
                    end;
                  Result := Result and CheckLength(O.AsArray.Length, p, objpath);

                end;
            else
              Result := false;
              if Assigned(callback) then
                callback(sender, veRuleMalformated, objpath);
            end;
          dtNumber:
            case ObjectGetType(O) of
              stInt, stDouble, stCurrency:
                begin
                  Result := Result and CheckRange(O, p, objpath);
                end;
            else
              if Assigned(callback) then
                callback(sender, veInvalidDataType, objpath);
              Result := false;
            end;
          dtText:
            case ObjectGetType(O) of
              stInt, stDouble, stCurrency, stString:
                begin
                  Result := Result and CheckLength(Length(O.AsString), p, objpath);
                  Result := Result and CheckRange(O, p, objpath);
                end;
            else
              if Assigned(callback) then
                callback(sender, veInvalidDataType, objpath);
              Result := false;
            end;
          dtScalar:
            case ObjectGetType(O) of
              stBoolean, stDouble, stCurrency, stInt, stString:
                begin
                  Result := Result and CheckLength(Length(O.AsString), p, objpath);
                  Result := Result and CheckRange(O, p, objpath);
                end;
            else
              if Assigned(callback) then
                callback(sender, veInvalidDataType, objpath);
              Result := false;
            end;
          dtAny:
            ;
        else
          if Assigned(callback) then
            callback(sender, veRuleMalformated, objpath);
          Result := false;
        end;
      Result := Result and CheckEnum(O, p, objpath)

    end;

  var
    j: Integer;

  begin
    Result := false;
    datatypes := TSuperObject.Create(stObject);
    names := TSuperObject.Create;
    try
      datatypes.I['str'] := Ord(dtStr);
      datatypes.I['int'] := Ord(dtInt);
      datatypes.I['float'] := Ord(dtFloat);
      datatypes.I['number'] := Ord(dtNumber);
      datatypes.I['text'] := Ord(dtText);
      datatypes.I['bool'] := Ord(dtBool);
      datatypes.I['map'] := Ord(dtMap);
      datatypes.I['seq'] := Ord(dtSeq);
      datatypes.I['scalar'] := Ord(dtScalar);
      datatypes.I['any'] := Ord(dtAny);

      if ObjectIsType(defs, stArray) then
        for j := 0 to defs.AsArray.Length - 1 do
          if ObjectIsType(defs.AsArray[j], stObject) then
            GetNames(defs.AsArray[j])
          else
          begin
            if Assigned(callback) then
              callback(sender, veRuleMalformated, '');
            Exit;
          end;

      if ObjectIsType(rules, stObject) then
        GetNames(rules)
      else
      begin
        if Assigned(callback) then
          callback(sender, veRuleMalformated, '');
        Exit;
      end;

      Result := process(Self, rules);

    finally
      datatypes := nil;
      names := nil;
    end;
  end;

  function TSuperObject._AddRef: Integer; stdcall;
  begin
    Result := InterlockedIncrement(FRefCount);
  end;

  function TSuperObject._Release: Integer; stdcall;
  begin
    Result := InterlockedDecrement(FRefCount);
    if Result = 0 then
      Destroy;
  end;

  function TSuperObject.Compare(const str: SOString): TSuperCompareResult;
  begin
    Result := Compare(TSuperObject.ParseString(PSOChar(str), false));
  end;

  function TSuperObject.Compare(const Obj: ISuperObject): TSuperCompareResult;
    function GetIntCompResult(const I: Int64): TSuperCompareResult;
    begin
      if I < 0 then
        Result := cpLess
      else if I = 0 then
        Result := cpEqu
      else
        Result := cpGreat;
    end;

    function GetDblCompResult(const D: Double): TSuperCompareResult;
    begin
      if D < 0 then
        Result := cpLess
      else if D = 0 then
        Result := cpEqu
      else
        Result := cpGreat;
    end;

  begin
    case dataType of
      stBoolean:
        case ObjectGetType(Obj) of
          stBoolean:
            Result := GetIntCompResult(Ord(FO.c_Boolean) - Ord(Obj.AsBoolean));
          stDouble:
            Result := GetDblCompResult(Ord(FO.c_Boolean) - Obj.AsDouble);
          stCurrency:
            Result := GetDblCompResult(Ord(FO.c_Boolean) - Obj.AsCurrency);
          stInt:
            Result := GetIntCompResult(Ord(FO.c_Boolean) - Obj.AsInteger);
          stString:
            Result := GetIntCompResult(StrComp(PSOChar(AsString), PSOChar(Obj.AsString)));
        else
          Result := cpError;
        end;
      stDouble:
        case ObjectGetType(Obj) of
          stBoolean:
            Result := GetDblCompResult(FO.c_double - Ord(Obj.AsBoolean));
          stDouble:
            Result := GetDblCompResult(FO.c_double - Obj.AsDouble);
          stCurrency:
            Result := GetDblCompResult(FO.c_double - Obj.AsCurrency);
          stInt:
            Result := GetDblCompResult(FO.c_double - Obj.AsInteger);
          stString:
            Result := GetIntCompResult(StrComp(PSOChar(AsString), PSOChar(Obj.AsString)));
        else
          Result := cpError;
        end;
      stCurrency:
        case ObjectGetType(Obj) of
          stBoolean:
            Result := GetDblCompResult(FO.c_currency - Ord(Obj.AsBoolean));
          stDouble:
            Result := GetDblCompResult(FO.c_currency - Obj.AsDouble);
          stCurrency:
            Result := GetDblCompResult(FO.c_currency - Obj.AsCurrency);
          stInt:
            Result := GetDblCompResult(FO.c_currency - Obj.AsInteger);
          stString:
            Result := GetIntCompResult(StrComp(PSOChar(AsString), PSOChar(Obj.AsString)));
        else
          Result := cpError;
        end;
      stInt:
        case ObjectGetType(Obj) of
          stBoolean:
            Result := GetIntCompResult(FO.c_int - Ord(Obj.AsBoolean));
          stDouble:
            Result := GetDblCompResult(FO.c_int - Obj.AsDouble);
          stCurrency:
            Result := GetDblCompResult(FO.c_int - Obj.AsCurrency);
          stInt:
            Result := GetIntCompResult(FO.c_int - Obj.AsInteger);
          stString:
            Result := GetIntCompResult(StrComp(PSOChar(AsString), PSOChar(Obj.AsString)));
        else
          Result := cpError;
        end;
      stString:
        case ObjectGetType(Obj) of
          stBoolean, stDouble, stCurrency, stInt, stString:
            Result := GetIntCompResult(StrComp(PSOChar(AsString), PSOChar(Obj.AsString)));
        else
          Result := cpError;
        end;
    else
      Result := cpError;
    end;
  end;

{$IFDEF SUPER_METHOD}

  function TSuperObject.AsMethod: TSuperMethod;
  begin
    if FDataType = stMethod then
      Result := FO.c_method
    else
      Result := nil;
  end;
{$ENDIF}
{$IFDEF SUPER_METHOD}

  constructor TSuperObject.Create(M: TSuperMethod);
  begin
    Create(stMethod);
    FO.c_method := M;
  end;
{$ENDIF}
{$IFDEF SUPER_METHOD}

  function TSuperObject.GetM(const path: SOString): TSuperMethod;
  var
    v: ISuperObject;
  begin
    v := ParseString(PSOChar(path), false, true, Self);
    if (v <> nil) and (ObjectGetType(v) = stMethod) then
      Result := v.AsMethod
    else
      Result := nil;
  end;
{$ENDIF}
{$IFDEF SUPER_METHOD}

  procedure TSuperObject.PutM(const path: SOString; value: TSuperMethod);
  begin
    ParseString(PSOChar(path), false, true, Self, [foCreatePath, foPutvalue], TSuperObject.Create(value));
  end;
{$ENDIF}
{$IFDEF SUPER_METHOD}

  function TSuperObject.call(const path: SOString; const param: ISuperObject): ISuperObject;
  begin
    Result := ParseString(PSOChar(path), false, true, Self, [foCallMethod], param);
  end;
{$ENDIF}
{$IFDEF SUPER_METHOD}

  function TSuperObject.call(const path, param: SOString): ISuperObject;
  begin
    Result := ParseString(PSOChar(path), false, true, Self, [foCallMethod], TSuperObject.ParseString(PSOChar(param), false));
  end;
{$ENDIF}

  function TSuperObject.GetProcessing: Boolean;
  begin
    Result := FProcessing;
  end;

  procedure TSuperObject.SetDataPtr(const value: Pointer);
  begin
    FDataPtr := value;
  end;

  procedure TSuperObject.SetProcessing(value: Boolean);
  begin
    FProcessing := value;
  end;

  { TSuperArray }

  function TSuperArray.Add(const Data: ISuperObject): Integer;
  begin
    Result := FLength;
    PutO(Result, Data);
  end;

  function TSuperArray.Add(Data: SuperInt): Integer;
  begin
    Result := Add(TSuperObject.Create(Data));
  end;

  function TSuperArray.Add(const Data: SOString): Integer;
  begin
    Result := Add(TSuperObject.Create(Data));
  end;

  function TSuperArray.Add(Data: Boolean): Integer;
  begin
    Result := Add(TSuperObject.Create(Data));
  end;

  function TSuperArray.Add(Data: Double): Integer;
  begin
    Result := Add(TSuperObject.Create(Data));
  end;

  function TSuperArray.AddC(const Data: Currency): Integer;
  begin
    Result := Add(TSuperObject.CreateCurrency(Data));
  end;

  function TSuperArray.Delete(index: Integer): ISuperObject;
  begin
    if (Index >= 0) and (Index < FLength) then
    begin
      Result := FArray^[index];
      FArray^[index] := nil;
      dec(FLength);
      if Index < FLength then
      begin
        Move(FArray^[index + 1], FArray^[index], (FLength - index) * sizeof(Pointer));
        Pointer(FArray^[FLength]) := nil;
      end;
    end;
  end;

  procedure TSuperArray.Insert(index: Integer; const value: ISuperObject);
  begin
    if (Index >= 0) then
      if (index < FLength) then
      begin
        if FLength = FSize then
          Expand(FLength);
        if Index < FLength then
          Move(FArray^[index], FArray^[index + 1], (FLength - index) * sizeof(Pointer));
        Pointer(FArray^[index]) := nil;
        FArray^[index] := value;
        Inc(FLength);
      end
      else
        PutO(index, value);
  end;

  procedure TSuperArray.Clear(all: Boolean);
  var
    j: Integer;
  begin
    for j := 0 to FLength - 1 do
      if FArray^[j] <> nil then
      begin
        if all then
          FArray^[j].Clear(all);
        FArray^[j] := nil;
      end;
    FLength := 0;
  end;

  procedure TSuperArray.Pack(all: Boolean);
  var
    PackedCount, StartIndex, EndIndex, j: Integer;
  begin
    if FLength > 0 then
    begin
      PackedCount := 0;
      StartIndex := 0;
      repeat
        while (StartIndex < FLength) and (FArray^[StartIndex] = nil) do
          Inc(StartIndex);
        if StartIndex < FLength then
        begin
          EndIndex := StartIndex;
          while (EndIndex < FLength) and (FArray^[EndIndex] <> nil) do
            Inc(EndIndex);

          dec(EndIndex);

          if StartIndex > PackedCount then
            Move(FArray^[StartIndex], FArray^[PackedCount], (EndIndex - StartIndex + 1) * sizeof(Pointer));

          Inc(PackedCount, EndIndex - StartIndex + 1);
          StartIndex := EndIndex + 1;
        end;
      until StartIndex >= FLength;
      FillChar(FArray^[PackedCount], (FLength - PackedCount) * sizeof(Pointer), 0);
      FLength := PackedCount;
      if all then
        for j := 0 to FLength - 1 do
          FArray^[j].Pack(all);
    end;
  end;

  constructor TSuperArray.Create;
  begin
    inherited Create;
    FSize := SUPER_ARRAY_LIST_DEFAULT_SIZE;
    FLength := 0;
    GetMem(FArray, sizeof(Pointer) * FSize);
    FillChar(FArray^, sizeof(Pointer) * FSize, 0);
  end;

  destructor TSuperArray.Destroy;
  begin
    Clear;
    FreeMem(FArray);
    inherited;
  end;

  procedure TSuperArray.Expand(max: Integer);
  var
    new_size: Integer;
  begin
    if (max < FSize) then
      Exit;
    if max < (FSize shl 1) then
      new_size := (FSize shl 1)
    else
      new_size := max + 1;
    ReallocMem(FArray, new_size * sizeof(Pointer));
    FillChar(FArray^[FSize], (new_size - FSize) * sizeof(Pointer), 0);
    FSize := new_size;
  end;

  function TSuperArray.GetO(const index: Integer): ISuperObject;
  begin
    if (index >= FLength) then
      Result := nil
    else
      Result := FArray^[index];
  end;

  function TSuperArray.GetB(const index: Integer): Boolean;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(index);
    if Obj <> nil then
      Result := Obj.AsBoolean
    else
      Result := false;
  end;

  function TSuperArray.GetD(const index: Integer): Double;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(index);
    if Obj <> nil then
      Result := Obj.AsDouble
    else
      Result := 0.0;
  end;

  function TSuperArray.GetI(const index: Integer): SuperInt;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(index);
    if Obj <> nil then
      Result := Obj.AsInteger
    else
      Result := 0;
  end;

  function TSuperArray.GetS(const index: Integer): SOString;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(index);
    if Obj <> nil then
      Result := Obj.AsString
    else
      Result := '';
  end;

  procedure TSuperArray.PutO(const index: Integer; const value: ISuperObject);
  begin
    Expand(index);
    FArray^[index] := value;
    if (FLength <= index) then
      FLength := index + 1;
  end;

  function TSuperArray.GetN(const index: Integer): ISuperObject;
  begin
    Result := GetO(index);
    if Result = nil then
      Result := TSuperObject.Create(stNull);
  end;

  procedure TSuperArray.PutN(const index: Integer; const value: ISuperObject);
  begin
    if value <> nil then
      PutO(index, value)
    else
      PutO(index, TSuperObject.Create(stNull));
  end;

  procedure TSuperArray.PutB(const index: Integer; value: Boolean);
  begin
    PutO(index, TSuperObject.Create(value));
  end;

  procedure TSuperArray.PutD(const index: Integer; value: Double);
  begin
    PutO(index, TSuperObject.Create(value));
  end;

  function TSuperArray.GetC(const index: Integer): Currency;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(index);
    if Obj <> nil then
      Result := Obj.AsCurrency
    else
      Result := 0.0;
  end;

  procedure TSuperArray.PutC(const index: Integer; value: Currency);
  begin
    PutO(index, TSuperObject.CreateCurrency(value));
  end;

  procedure TSuperArray.PutI(const index: Integer; value: SuperInt);
  begin
    PutO(index, TSuperObject.Create(value));
  end;

  procedure TSuperArray.PutS(const index: Integer; const value: SOString);
  begin
    PutO(index, TSuperObject.Create(value));
  end;

{$IFDEF SUPER_METHOD}

  function TSuperArray.GetM(const index: Integer): TSuperMethod;
  var
    v: ISuperObject;
  begin
    v := GetO(index);
    if (ObjectGetType(v) = stMethod) then
      Result := v.AsMethod
    else
      Result := nil;
  end;
{$ENDIF}
{$IFDEF SUPER_METHOD}

  procedure TSuperArray.PutM(const index: Integer; value: TSuperMethod);
  begin
    PutO(index, TSuperObject.Create(value));
  end;
{$ENDIF}
  { TSuperWriterString }

  function TSuperWriterString.Append(buf: PSOChar; Size: Integer): Integer;
    function max(A, B: Integer): Integer;
    begin
      if A > B then
        Result := A
      else
        Result := B
    end;

  begin
    Result := Size;
    if Size > 0 then
    begin
      if (FSize - FBPos <= Size) then
      begin
        FSize := max(FSize * 2, FBPos + Size + 8);
        ReallocMem(FBuf, FSize * sizeof(SOChar));
      end;
      // fast move
      case Size of
        1:
          FBuf[FBPos] := buf^;
        2:
          PInteger(@FBuf[FBPos])^ := PInteger(buf)^;
        4:
          PInt64(@FBuf[FBPos])^ := PInt64(buf)^;
      else
        Move(buf^, FBuf[FBPos], Size * sizeof(SOChar));
      end;
      Inc(FBPos, Size);
      FBuf[FBPos] := #0;
    end;
  end;

  function TSuperWriterString.Append(buf: PSOChar): Integer;
  begin
    Result := Append(buf, StrLen(buf));
  end;

  constructor TSuperWriterString.Create;
  begin
    inherited;
    FSize := 32;
    FBPos := 0;
    GetMem(FBuf, FSize * sizeof(SOChar));
  end;

  destructor TSuperWriterString.Destroy;
  begin
    inherited;
    if FBuf <> nil then
      FreeMem(FBuf)
  end;

  function TSuperWriterString.GetString: SOString;
  begin
    SetString(Result, FBuf, FBPos);
  end;

  procedure TSuperWriterString.Reset;
  begin
    FBuf[0] := #0;
    FBPos := 0;
  end;

  procedure TSuperWriterString.TrimRight;
  begin
    while (FBPos > 0) and (FBuf[FBPos - 1] < #256) and (AnsiChar(FBuf[FBPos - 1]) in [#32, #13, #10]) do
    begin
      dec(FBPos);
      FBuf[FBPos] := #0;
    end;
  end;

  { TSuperWriterStream }

  function TSuperWriterStream.Append(buf: PSOChar): Integer;
  begin
    Result := Append(buf, StrLen(buf));
  end;

  constructor TSuperWriterStream.Create(AStream: TStream);
  begin
    inherited Create;
    FStream := AStream;
  end;

  procedure TSuperWriterStream.Reset;
  begin
    FStream.Size := 0;
  end;

  { TSuperWriterStream }

  function TSuperAnsiWriterStream.Append(buf: PSOChar; Size: Integer): Integer;
  var
    Buffer: array [0 .. 1023] of AnsiChar;
    pBuffer: PAnsiChar;
    I: Integer;
  begin
    if Size = 1 then
      Result := FStream.Write(buf^, Size)
    else
    begin
      if Size > sizeof(Buffer) then
        GetMem(pBuffer, Size)
      else
        pBuffer := @Buffer;
      try
        for I := 0 to Size - 1 do
          pBuffer[I] := AnsiChar(buf[I]);
        Result := FStream.Write(pBuffer^, Size);
      finally
        if pBuffer <> @Buffer then
          FreeMem(pBuffer);
      end;
    end;
  end;

  { TSuperUnicodeWriterStream }

  function TSuperUnicodeWriterStream.Append(buf: PSOChar; Size: Integer): Integer;
  begin
    Result := FStream.Write(buf^, Size * 2);
  end;

  { TSuperWriterFake }

  function TSuperWriterFake.Append(buf: PSOChar; Size: Integer): Integer;
  begin
    Inc(FSize, Size);
    Result := FSize;
  end;

  function TSuperWriterFake.Append(buf: PSOChar): Integer;
  begin
    Inc(FSize, StrLen(buf));
    Result := FSize;
  end;

  constructor TSuperWriterFake.Create;
  begin
    inherited Create;
    FSize := 0;
  end;

  procedure TSuperWriterFake.Reset;
  begin
    FSize := 0;
  end;

  { TSuperWriterSock }

  function TSuperWriterSock.Append(buf: PSOChar; Size: Integer): Integer;
  var
    Buffer: array [0 .. 1023] of AnsiChar;
    pBuffer: PAnsiChar;
    I: Integer;
  begin
    if Size = 1 then
{$IFDEF FPC}
      Result := fpsend(FSocket, buf, Size, 0)
    else
{$ELSE}
      Result := send(FSocket, buf^, Size, 0)
    else
{$ENDIF}
    begin
      if Size > sizeof(Buffer) then
        GetMem(pBuffer, Size)
      else
        pBuffer := @Buffer;
      try
        for I := 0 to Size - 1 do
          pBuffer[I] := AnsiChar(buf[I]);
{$IFDEF FPC}
        Result := fpsend(FSocket, pBuffer, Size, 0);
{$ELSE}
        Result := send(FSocket, pBuffer^, Size, 0);
{$ENDIF}
      finally
        if pBuffer <> @Buffer then
          FreeMem(pBuffer);
      end;
    end;
    Inc(FSize, Result);
  end;

  function TSuperWriterSock.Append(buf: PSOChar): Integer;
  begin
    Result := Append(buf, StrLen(buf));
  end;

  constructor TSuperWriterSock.Create(ASocket: Integer);
  begin
    inherited Create;
    FSocket := ASocket;
    FSize := 0;
  end;

  procedure TSuperWriterSock.Reset;
  begin
    FSize := 0;
  end;

  { TSuperTokenizer }

  constructor TSuperTokenizer.Create;
  begin
    pb := TSuperWriterString.Create;
    line := 1;
    col := 0;
    Reset;
  end;

  destructor TSuperTokenizer.Destroy;
  begin
    Reset;
    pb.free;
    inherited;
  end;

  procedure TSuperTokenizer.Reset;
  var
    I: Integer;
  begin
    for I := depth downto 0 do
      ResetLevel(I);
    depth := 0;
    err := teSuccess;
  end;

  procedure TSuperTokenizer.ResetLevel(adepth: Integer);
  begin
    stack[adepth].state := tsEatws;
    stack[adepth].saved_state := tsStart;
    stack[adepth].Current := nil;
    stack[adepth].field_name := '';
    stack[adepth].Obj := nil;
    stack[adepth].parent := nil;
    stack[adepth].gparent := nil;
  end;

  { TSuperAvlTree }

  constructor TSuperAvlTree.Create;
  begin
    FRoot := nil;
    FCount := 0;
  end;

  destructor TSuperAvlTree.Destroy;
  begin
    Clear;
    inherited;
  end;

  function TSuperAvlTree.IsEmpty: Boolean;
  begin
    Result := FRoot = nil;
  end;

  function TSuperAvlTree.balance(bal: TSuperAvlEntry): TSuperAvlEntry;
  var
    deep, old: TSuperAvlEntry;
    bf: Integer;
  begin
    if (bal.FBf > 0) then
    begin
      deep := bal.FGt;
      if (deep.FBf < 0) then
      begin
        old := bal;
        bal := deep.FLt;
        old.FGt := bal.FLt;
        deep.FLt := bal.FGt;
        bal.FLt := old;
        bal.FGt := deep;
        bf := bal.FBf;
        if (bf <> 0) then
        begin
          if (bf > 0) then
          begin
            old.FBf := -1;
            deep.FBf := 0;
          end
          else
          begin
            deep.FBf := 1;
            old.FBf := 0;
          end;
          bal.FBf := 0;
        end
        else
        begin
          old.FBf := 0;
          deep.FBf := 0;
        end;
      end
      else
      begin
        bal.FGt := deep.FLt;
        deep.FLt := bal;
        if (deep.FBf = 0) then
        begin
          deep.FBf := -1;
          bal.FBf := 1;
        end
        else
        begin
          deep.FBf := 0;
          bal.FBf := 0;
        end;
        bal := deep;
      end;
    end
    else
    begin
      (* "Less than" subtree is deeper. *)

      deep := bal.FLt;
      if (deep.FBf > 0) then
      begin
        old := bal;
        bal := deep.FGt;
        old.FLt := bal.FGt;
        deep.FGt := bal.FLt;
        bal.FGt := old;
        bal.FLt := deep;

        bf := bal.FBf;
        if (bf <> 0) then
        begin
          if (bf < 0) then
          begin
            old.FBf := 1;
            deep.FBf := 0;
          end
          else
          begin
            deep.FBf := -1;
            old.FBf := 0;
          end;
          bal.FBf := 0;
        end
        else
        begin
          old.FBf := 0;
          deep.FBf := 0;
        end;
      end
      else
      begin
        bal.FLt := deep.FGt;
        deep.FGt := bal;
        if (deep.FBf = 0) then
        begin
          deep.FBf := 1;
          bal.FBf := -1;
        end
        else
        begin
          deep.FBf := 0;
          bal.FBf := 0;
        end;
        bal := deep;
      end;
    end;
    Result := bal;
  end;

  function TSuperAvlTree.Insert(h: TSuperAvlEntry): TSuperAvlEntry;
  var
    unbal, parentunbal, hh, parent: TSuperAvlEntry;
    depth, unbaldepth: LongInt;
    cmp: Integer;
    unbalbf: Integer;
    branch: TSuperAvlBitArray;
    p: Pointer;
  begin
    Inc(FCount);
    h.FLt := nil;
    h.FGt := nil;
    h.FBf := 0;
    branch := [];

    if (FRoot = nil) then
      FRoot := h
    else
    begin
      unbal := nil;
      parentunbal := nil;
      depth := 0;
      unbaldepth := 0;
      hh := FRoot;
      parent := nil;
      repeat
        if (hh.FBf <> 0) then
        begin
          unbal := hh;
          parentunbal := parent;
          unbaldepth := depth;
        end;
        if hh.FHash <> h.FHash then
        begin
          if hh.FHash < h.FHash then
            cmp := -1
          else if hh.FHash > h.FHash then
            cmp := 1
          else
            cmp := 0;
        end
        else
          cmp := CompareNodeNode(h, hh);
        if (cmp = 0) then
        begin
          Result := hh;
          // exchange data
          p := hh.Ptr;
          hh.FPtr := h.Ptr;
          h.FPtr := p;
          doDeleteEntry(h, false);
          dec(FCount);
          Exit;
        end;
        parent := hh;
        if (cmp > 0) then
        begin
          hh := hh.FGt;
          include(branch, depth);
        end
        else
        begin
          hh := hh.FLt;
          exclude(branch, depth);
        end;
        Inc(depth);
      until (hh = nil);

      if (cmp < 0) then
        parent.FLt := h
      else
        parent.FGt := h;

      depth := unbaldepth;

      if (unbal = nil) then
        hh := FRoot
      else
      begin
        if depth in branch then
          cmp := 1
        else
          cmp := -1;
        Inc(depth);
        unbalbf := unbal.FBf;
        if (cmp < 0) then
          dec(unbalbf)
        else
          Inc(unbalbf);
        if cmp < 0 then
          hh := unbal.FLt
        else
          hh := unbal.FGt;
        if ((unbalbf <> -2) and (unbalbf <> 2)) then
        begin
          unbal.FBf := unbalbf;
          unbal := nil;
        end;
      end;

      if (hh <> nil) then
        while (h <> hh) do
        begin
          if depth in branch then
            cmp := 1
          else
            cmp := -1;
          Inc(depth);
          if (cmp < 0) then
          begin
            hh.FBf := -1;
            hh := hh.FLt;
          end
          else (* cmp > 0 *)
          begin
            hh.FBf := 1;
            hh := hh.FGt;
          end;
        end;

      if (unbal <> nil) then
      begin
        unbal := balance(unbal);
        if (parentunbal = nil) then
          FRoot := unbal
        else
        begin
          depth := unbaldepth - 1;
          if depth in branch then
            cmp := 1
          else
            cmp := -1;
          if (cmp < 0) then
            parentunbal.FLt := unbal
          else
            parentunbal.FGt := unbal;
        end;
      end;
    end;
    Result := h;
  end;

  function TSuperAvlTree.Search(const k: SOString; st: TSuperAvlSearchTypes): TSuperAvlEntry;
  var
    cmp, target_cmp: Integer;
    match_h, h: TSuperAvlEntry;
    ha: Cardinal;
  begin
    ha := TSuperAvlEntry.Hash(k);

    match_h := nil;
    h := FRoot;

    if (stLess in st) then
      target_cmp := 1
    else if (stGreater in st) then
      target_cmp := -1
    else
      target_cmp := 0;

    while (h <> nil) do
    begin
      if h.FHash < ha then
        cmp := -1
      else if h.FHash > ha then
        cmp := 1
      else
        cmp := 0;

      if cmp = 0 then
        cmp := CompareKeyNode(PSOChar(k), h);
      if (cmp = 0) then
      begin
        if (stEQual in st) then
        begin
          match_h := h;
          Break;
        end;
        cmp := -target_cmp;
      end
      else if (target_cmp <> 0) then
        if ((cmp xor target_cmp) and SUPER_AVL_MASK_HIGH_BIT) = 0 then
          match_h := h;
      if cmp < 0 then
        h := h.FLt
      else
        h := h.FGt;
    end;
    Result := match_h;
  end;

  function TSuperAvlTree.Delete(const k: SOString): ISuperObject;
  var
    depth, rm_depth: LongInt;
    branch: TSuperAvlBitArray;
    h, parent, child, path, rm, parent_rm: TSuperAvlEntry;
    cmp, cmp_shortened_sub_with_path, reduced_depth, bf: Integer;
    ha: Cardinal;
  begin
    ha := TSuperAvlEntry.Hash(k);
    cmp_shortened_sub_with_path := 0;
    branch := [];

    depth := 0;
    h := FRoot;
    parent := nil;
    while true do
    begin
      if (h = nil) then
        Exit;
      if h.FHash < ha then
        cmp := -1
      else if h.FHash > ha then
        cmp := 1
      else
        cmp := 0;

      if cmp = 0 then
        cmp := CompareKeyNode(k, h);
      if (cmp = 0) then
        Break;
      parent := h;
      if (cmp > 0) then
      begin
        h := h.FGt;
        include(branch, depth)
      end
      else
      begin
        h := h.FLt;
        exclude(branch, depth)
      end;
      Inc(depth);
      cmp_shortened_sub_with_path := cmp;
    end;
    rm := h;
    parent_rm := parent;
    rm_depth := depth;

    if (h.FBf < 0) then
    begin
      child := h.FLt;
      exclude(branch, depth);
      cmp := -1;
    end
    else
    begin
      child := h.FGt;
      include(branch, depth);
      cmp := 1;
    end;
    Inc(depth);

    if (child <> nil) then
    begin
      cmp := -cmp;
      repeat
        parent := h;
        h := child;
        if (cmp < 0) then
        begin
          child := h.FLt;
          exclude(branch, depth);
        end
        else
        begin
          child := h.FGt;
          include(branch, depth);
        end;
        Inc(depth);
      until (child = nil);

      if (parent = rm) then
        cmp_shortened_sub_with_path := -cmp
      else
        cmp_shortened_sub_with_path := cmp;

      if cmp > 0 then
        child := h.FLt
      else
        child := h.FGt;
    end;

    if (parent = nil) then
      FRoot := child
    else if (cmp_shortened_sub_with_path < 0) then
      parent.FLt := child
    else
      parent.FGt := child;

    if parent = rm then
      path := h
    else
      path := parent;

    if (h <> rm) then
    begin
      h.FLt := rm.FLt;
      h.FGt := rm.FGt;
      h.FBf := rm.FBf;
      if (parent_rm = nil) then
        FRoot := h
      else
      begin
        depth := rm_depth - 1;
        if (depth in branch) then
          parent_rm.FGt := h
        else
          parent_rm.FLt := h;
      end;
    end;

    if (path <> nil) then
    begin
      h := FRoot;
      parent := nil;
      depth := 0;
      while (h <> path) do
      begin
        if (depth in branch) then
        begin
          child := h.FGt;
          h.FGt := parent;
        end
        else
        begin
          child := h.FLt;
          h.FLt := parent;
        end;
        Inc(depth);
        parent := h;
        h := child;
      end;

      reduced_depth := 1;
      cmp := cmp_shortened_sub_with_path;
      while true do
      begin
        if (reduced_depth <> 0) then
        begin
          bf := h.FBf;
          if (cmp < 0) then
            Inc(bf)
          else
            dec(bf);
          if ((bf = -2) or (bf = 2)) then
          begin
            h := balance(h);
            bf := h.FBf;
          end
          else
            h.FBf := bf;
          reduced_depth := Integer(bf = 0);
        end;
        if (parent = nil) then
          Break;
        child := h;
        h := parent;
        dec(depth);
        if depth in branch then
          cmp := 1
        else
          cmp := -1;
        if (cmp < 0) then
        begin
          parent := h.FLt;
          h.FLt := child;
        end
        else
        begin
          parent := h.FGt;
          h.FGt := child;
        end;
      end;
      FRoot := h;
    end;
    if rm <> nil then
    begin
      Result := rm.Getvalue;
      doDeleteEntry(rm, false);
      dec(FCount);
    end;
  end;

  procedure TSuperAvlTree.Pack(all: Boolean);
  var
    node1, node2: TSuperAvlEntry;
    list: TList;
    I: Integer;
  begin
    node1 := FRoot;
    list := TList.Create;
    while node1 <> nil do
    begin
      if (node1.FLt = nil) then
      begin
        node2 := node1.FGt;
        if (node1.FPtr = nil) then
          list.Add(node1)
        else if all then
          node1.value.Pack(all);
      end
      else
      begin
        node2 := node1.FLt;
        node1.FLt := node2.FGt;
        node2.FGt := node1;
      end;
      node1 := node2;
    end;
    for I := 0 to list.count - 1 do
      Delete(TSuperAvlEntry(list[I]).FName);
    list.free;
  end;

  procedure TSuperAvlTree.Clear(all: Boolean);
  var
    node1, node2: TSuperAvlEntry;
  begin
    node1 := FRoot;
    while node1 <> nil do
    begin
      if (node1.FLt = nil) then
      begin
        node2 := node1.FGt;
        doDeleteEntry(node1, all);
      end
      else
      begin
        node2 := node1.FLt;
        node1.FLt := node2.FGt;
        node2.FGt := node1;
      end;
      node1 := node2;
    end;
    FRoot := nil;
    FCount := 0;
  end;

  function TSuperAvlTree.CompareKeyNode(const k: SOString; h: TSuperAvlEntry): Integer;
  begin
    Result := StrComp(PSOChar(k), PSOChar(h.FName));
  end;

  function TSuperAvlTree.CompareNodeNode(node1, node2: TSuperAvlEntry): Integer;
  begin
    Result := StrComp(PSOChar(node1.FName), PSOChar(node2.FName));
  end;

  { TSuperAvlIterator }

  (* Initialize depth to invalid value, to indicate iterator is
    ** invalid.   (Depth is zero-base.)  It's not necessary to initialize
    ** iterators prior to passing them to the "start" function.
  *)

  constructor TSuperAvlIterator.Create(tree: TSuperAvlTree);
  begin
    FDepth := not 0;
    FTree := tree;
  end;

  procedure TSuperAvlIterator.Search(const k: SOString; st: TSuperAvlSearchTypes);
  var
    h: TSuperAvlEntry;
    D: LongInt;
    cmp, target_cmp: Integer;
    ha: Cardinal;
  begin
    ha := TSuperAvlEntry.Hash(k);
    h := FTree.FRoot;
    D := 0;
    FDepth := not 0;
    if (h = nil) then
      Exit;

    if (stLess in st) then
      target_cmp := 1
    else if (stGreater in st) then
      target_cmp := -1
    else
      target_cmp := 0;

    while true do
    begin
      if h.FHash < ha then
        cmp := -1
      else if h.FHash > ha then
        cmp := 1
      else
        cmp := 0;

      if cmp = 0 then
        cmp := FTree.CompareKeyNode(k, h);
      if (cmp = 0) then
      begin
        if (stEQual in st) then
        begin
          FDepth := D;
          Break;
        end;
        cmp := -target_cmp;
      end
      else if (target_cmp <> 0) then
        if ((cmp xor target_cmp) and SUPER_AVL_MASK_HIGH_BIT) = 0 then
          FDepth := D;
      if cmp < 0 then
        h := h.FLt
      else
        h := h.FGt;
      if (h = nil) then
        Break;
      if (cmp > 0) then
        include(FBranch, D)
      else
        exclude(FBranch, D);
      FPath[D] := h;
      Inc(D);
    end;
  end;

  procedure TSuperAvlIterator.First;
  var
    h: TSuperAvlEntry;
  begin
    h := FTree.FRoot;
    FDepth := not 0;
    FBranch := [];
    while (h <> nil) do
    begin
      if (FDepth <> not 0) then
        FPath[FDepth] := h;
      Inc(FDepth);
      h := h.FLt;
    end;
  end;

  procedure TSuperAvlIterator.Last;
  var
    h: TSuperAvlEntry;
  begin
    h := FTree.FRoot;
    FDepth := not 0;
    FBranch := [0 .. SUPER_AVL_MAX_DEPTH - 1];
    while (h <> nil) do
    begin
      if (FDepth <> not 0) then
        FPath[FDepth] := h;
      Inc(FDepth);
      h := h.FGt;
    end;
  end;

  function TSuperAvlIterator.MoveNext: Boolean;
  begin
    if FDepth = not 0 then
      First
    else
      Next;
    Result := GetIter <> nil;
  end;

  function TSuperAvlIterator.GetIter: TSuperAvlEntry;
  begin
    if (FDepth = not 0) then
    begin
      Result := nil;
      Exit;
    end;
    if FDepth = 0 then
      Result := FTree.FRoot
    else
      Result := FPath[FDepth - 1];
  end;

  procedure TSuperAvlIterator.Next;
  var
    h: TSuperAvlEntry;
  begin
    if (FDepth <> not 0) then
    begin
      if FDepth = 0 then
        h := FTree.FRoot.FGt
      else
        h := FPath[FDepth - 1].FGt;

      if (h = nil) then
        repeat
          if (FDepth = 0) then
          begin
            FDepth := not 0;
            Break;
          end;
          dec(FDepth);
        until (not(FDepth in FBranch))
      else
      begin
        include(FBranch, FDepth);
        FPath[FDepth] := h;
        Inc(FDepth);
        while true do
        begin
          h := h.FLt;
          if (h = nil) then
            Break;
          exclude(FBranch, FDepth);
          FPath[FDepth] := h;
          Inc(FDepth);
        end;
      end;
    end;
  end;

  procedure TSuperAvlIterator.Prior;
  var
    h: TSuperAvlEntry;
  begin
    if (FDepth <> not 0) then
    begin
      if FDepth = 0 then
        h := FTree.FRoot.FLt
      else
        h := FPath[FDepth - 1].FLt;
      if (h = nil) then
        repeat
          if (FDepth = 0) then
          begin
            FDepth := not 0;
            Break;
          end;
          dec(FDepth);
        until (FDepth in FBranch)
      else
      begin
        exclude(FBranch, FDepth);
        FPath[FDepth] := h;
        Inc(FDepth);
        while true do
        begin
          h := h.FGt;
          if (h = nil) then
            Break;
          include(FBranch, FDepth);
          FPath[FDepth] := h;
          Inc(FDepth);
        end;
      end;
    end;
  end;

  procedure TSuperAvlTree.doDeleteEntry(Entry: TSuperAvlEntry; all: Boolean);
  begin
    Entry.free;
  end;

  function TSuperAvlTree.GetEnumerator: TSuperAvlIterator;
  begin
    Result := TSuperAvlIterator.Create(Self);
  end;

  { TSuperAvlEntry }

  constructor TSuperAvlEntry.Create(const AName: SOString; Obj: Pointer);
  begin
    FName := AName;
    FPtr := Obj;
    FHash := Hash(FName);
  end;

  function TSuperAvlEntry.Getvalue: ISuperObject;
  begin
    Result := ISuperObject(FPtr)
  end;

  class function TSuperAvlEntry.Hash(const k: SOString): Cardinal;
  var
    h: Cardinal;
    I: Integer;
  begin
    h := 0;
    for I := 1 to Length(k) do
      h := h * 129 + Ord(k[I]) + $9E370001;
    Result := h;
  end;

  procedure TSuperAvlEntry.Setvalue(const val: ISuperObject);
  begin
    ISuperObject(FPtr) := val;
  end;

  { TSuperTableString }

  function TSuperTableString.Getvalues: ISuperObject;
  var
    Ite: TSuperAvlIterator;
    Obj: TSuperAvlEntry;
  begin
    Result := TSuperObject.Create(stArray);
    Ite := TSuperAvlIterator.Create(Self);
    try
      Ite.First;
      Obj := Ite.GetIter;
      while Obj <> nil do
      begin
        Result.AsArray.Add(Obj.value);
        Ite.Next;
        Obj := Ite.GetIter;
      end;
    finally
      Ite.free;
    end;
  end;

  function TSuperTableString.GetNames: ISuperObject;
  var
    Ite: TSuperAvlIterator;
    Obj: TSuperAvlEntry;
  begin
    Result := TSuperObject.Create(stArray);
    Ite := TSuperAvlIterator.Create(Self);
    try
      Ite.First;
      Obj := Ite.GetIter;
      while Obj <> nil do
      begin
        Result.AsArray.Add(TSuperObject.Create(Obj.FName));
        Ite.Next;
        Obj := Ite.GetIter;
      end;
    finally
      Ite.free;
    end;
  end;

  procedure TSuperTableString.doDeleteEntry(Entry: TSuperAvlEntry; all: Boolean);
  begin
    if Entry.Ptr <> nil then
    begin
      if all then
        Entry.value.Clear(true);
      Entry.value := nil;
    end;
    inherited;
  end;

  function TSuperTableString.Find(const k: SOString; var value: ISuperObject): Boolean;
  var
    e: TSuperAvlEntry;
  begin
    e := Search(k);
    if e <> nil then
    begin
      value := e.value;
      Result := true;
    end
    else
      Result := false;
  end;

  function TSuperTableString.Exists(const k: SOString): Boolean;
  begin
    Result := Search(k) <> nil;
  end;

  function TSuperTableString.GetO(const k: SOString): ISuperObject;
  var
    e: TSuperAvlEntry;
  begin
    e := Search(k);
    if e <> nil then
      Result := e.value
    else
      Result := nil
  end;

  procedure TSuperTableString.PutO(const k: SOString; const value: ISuperObject);
  var
    Entry: TSuperAvlEntry;
  begin
    Entry := Insert(TSuperAvlEntry.Create(k, Pointer(value)));
    if Entry.FPtr <> nil then
      ISuperObject(Entry.FPtr)._AddRef;
  end;

  procedure TSuperTableString.PutS(const k: SOString; const value: SOString);
  begin
    PutO(k, TSuperObject.Create(value));
  end;

  function TSuperTableString.GetS(const k: SOString): SOString;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(k);
    if Obj <> nil then
      Result := Obj.AsString
    else
      Result := '';
  end;

  procedure TSuperTableString.PutI(const k: SOString; value: SuperInt);
  begin
    PutO(k, TSuperObject.Create(value));
  end;

  function TSuperTableString.GetI(const k: SOString): SuperInt;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(k);
    if Obj <> nil then
      Result := Obj.AsInteger
    else
      Result := 0;
  end;

  procedure TSuperTableString.PutD(const k: SOString; value: Double);
  begin
    PutO(k, TSuperObject.Create(value));
  end;

  procedure TSuperTableString.PutC(const k: SOString; value: Currency);
  begin
    PutO(k, TSuperObject.CreateCurrency(value));
  end;

  function TSuperTableString.GetC(const k: SOString): Currency;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(k);
    if Obj <> nil then
      Result := Obj.AsCurrency
    else
      Result := 0.0;
  end;

  function TSuperTableString.GetD(const k: SOString): Double;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(k);
    if Obj <> nil then
      Result := Obj.AsDouble
    else
      Result := 0.0;
  end;

  procedure TSuperTableString.PutB(const k: SOString; value: Boolean);
  begin
    PutO(k, TSuperObject.Create(value));
  end;

  function TSuperTableString.GetB(const k: SOString): Boolean;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(k);
    if Obj <> nil then
      Result := Obj.AsBoolean
    else
      Result := false;
  end;

{$IFDEF SUPER_METHOD}

  procedure TSuperTableString.PutM(const k: SOString; value: TSuperMethod);
  begin
    PutO(k, TSuperObject.Create(value));
  end;
{$ENDIF}
{$IFDEF SUPER_METHOD}

  function TSuperTableString.GetM(const k: SOString): TSuperMethod;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(k);
    if Obj <> nil then
      Result := Obj.AsMethod
    else
      Result := nil;
  end;
{$ENDIF}

  procedure TSuperTableString.PutN(const k: SOString; const value: ISuperObject);
  begin
    if value <> nil then
      PutO(k, TSuperObject.Create(stNull))
    else
      PutO(k, value);
  end;

  function TSuperTableString.GetN(const k: SOString): ISuperObject;
  var
    Obj: ISuperObject;
  begin
    Obj := GetO(k);
    if Obj <> nil then
      Result := Obj
    else
      Result := TSuperObject.Create(stNull);
  end;

{$IFDEF HAVE_RTTI}
  { TSuperAttribute }

  constructor TSuperAttribute.Create(const AName: string);
  begin
    FName := AName;
  end;

  { TSuperRttiContext }

  constructor TSuperRttiContext.Create;
  begin
    Context := TRttiContext.Create;
    SerialFromJson := TDictionary<PTypeInfo, TSerialFromJson>.Create;
    SerialToJson := TDictionary<PTypeInfo, TSerialToJson>.Create;

    SerialFromJson.Add(TypeInfo(Boolean), serialfromBoolean);
    SerialFromJson.Add(TypeInfo(TDateTime), serialfromdatetime);
    SerialFromJson.Add(TypeInfo(tguid), serialfromguid);
    SerialToJson.Add(TypeInfo(Boolean), serialtoBoolean);
    SerialToJson.Add(TypeInfo(TDateTime), serialtodatetime);
    SerialToJson.Add(TypeInfo(tguid), serialtoguid);
  end;

  destructor TSuperRttiContext.Destroy;
  begin
    SerialFromJson.free;
    SerialToJson.free;
    Context.free;
  end;

  class function TSuperRttiContext.GetFieldName(r: TRttiField): string;
  var
    O: TCustomAttribute;
  begin
    for O in r.GetAttributes do
      if O is SOName then
        Exit(SOName(O).name);
    Result := r.name;
  end;

  class function TSuperRttiContext.GetFieldDefault(r: TRttiField; const Obj: ISuperObject): ISuperObject;
  var
    O: TCustomAttribute;
  begin
    if not ObjectIsType(Obj, stNull) then
      Exit(Obj);
    for O in r.GetAttributes do
      if O is SODefault then
        Exit(SO(SODefault(O).name));
    Result := Obj;
  end;

  function TSuperRttiContext.AsType<T>(const Obj: ISuperObject): T;
  var
    ret: Tvalue;
  begin
    if FromJson(TypeInfo(T), Obj, ret) then
      Result := ret.AsType<T>
    else
      raise Exception.Create('Marshalling error');
  end;

  function TSuperRttiContext.AsJSon<T>(const Obj: T; const index: ISuperObject = nil): ISuperObject;
  var
    v: Tvalue;
  begin
    Tvalue.Make(@Obj, TypeInfo(T), v);
    if index <> nil then
      Result := ToJson(v, index)
    else
      Result := ToJson(v, SO);
  end;

  function TSuperRttiContext.FromJson(TypeInfo: PTypeInfo; const Obj: ISuperObject; var value: Tvalue): Boolean;

    procedure FromChar;
    begin
      if ObjectIsType(Obj, stString) and (Length(Obj.AsString) = 1) then
      begin
        value := string(AnsiString(Obj.AsString)[1]);
        Result := true;
      end
      else
        Result := false;
    end;

    procedure FromWideChar;
    begin
      if ObjectIsType(Obj, stString) and (Length(Obj.AsString) = 1) then
      begin
        value := Obj.AsString[1];
        Result := true;
      end
      else
        Result := false;
    end;

    procedure FromInt64;
    var
      I: Int64;
    begin
      case ObjectGetType(Obj) of
        stInt:
          begin
            Tvalue.Make(nil, TypeInfo, value);
            TvalueData(value).FAsSInt64 := Obj.AsInteger;
            Result := true;
          end;
        stString:
          begin
            if TryStrToInt64(Obj.AsString, I) then
            begin
              Tvalue.Make(nil, TypeInfo, value);
              TvalueData(value).FAsSInt64 := I;
              Result := true;
            end
            else
              Result := false;
          end;
      else
        Result := false;
      end;
    end;

    procedure FromInt(const Obj: ISuperObject);
    var
      TypeData: PTypeData;
      I: Integer;
      O: ISuperObject;
    begin
      case ObjectGetType(Obj) of
        stInt, stBoolean:
          begin
            I := Obj.AsInteger;
            TypeData := GetTypeData(TypeInfo);
            if TypeData.Maxvalue > TypeData.Minvalue then
              Result := (I >= TypeData.Minvalue) and (I <= TypeData.Maxvalue)
            else
              Result := (I >= TypeData.Minvalue) and (I <= Int64(PCardinal(@TypeData.Maxvalue)^));
            if Result then
              Tvalue.Make(@I, TypeInfo, value);
          end;
        stString:
          begin
            O := SO(Obj.AsString);
            if not ObjectIsType(O, stString) then
              FromInt(O)
            else
              Result := false;
          end;
      else
        Result := false;
      end;
    end;

    procedure fromSet;
    var
      I: Integer;
    begin
      case ObjectGetType(Obj) of
        stInt:
          begin
            Tvalue.Make(nil, TypeInfo, value);
            TvalueData(value).FAsSLong := Obj.AsInteger;
            Result := true;
          end;
        stString:
          begin
            if TryStrToInt(Obj.AsString, I) then
            begin
              Tvalue.Make(nil, TypeInfo, value);
              TvalueData(value).FAsSLong := I;
              Result := true;
            end
            else
              Result := false;
          end;
      else
        Result := false;
      end;
    end;

    procedure FromFloat(const Obj: ISuperObject);
    var
      O: ISuperObject;
    begin
      case ObjectGetType(Obj) of
        stInt, stDouble, stCurrency:
          begin
            Tvalue.Make(nil, TypeInfo, value);
            case GetTypeData(TypeInfo).FloatType of
              ftSingle:
                TvalueData(value).FAsSingle := Obj.AsDouble;
              ftDouble:
                TvalueData(value).FAsDouble := Obj.AsDouble;
              ftExtended:
                TvalueData(value).FAsExtended := Obj.AsDouble;
              ftComp:
                TvalueData(value).FAsSInt64 := Obj.AsInteger;
              ftCurr:
                TvalueData(value).FAsCurr := Obj.AsCurrency;
            end;
            Result := true;
          end;
        stString:
          begin
            O := SO(Obj.AsString);
            if not ObjectIsType(O, stString) then
              FromFloat(O)
            else
              Result := false;
          end
      else
        Result := false;
      end;
    end;

    procedure FromString;
    begin
      case ObjectGetType(Obj) of
        stObject, stArray:
          Result := false;
        stNull:
          begin
            value := '';
            Result := true;
          end;
      else
        value := Obj.AsString;
        Result := true;
      end;
    end;

    function trimName(N: string): string;
    begin
      if N.startswith('System.') then
        Result := Copy(N, 8)
      else
        Result := N;
    end;

    function TryfindType(N: string): TRttiType;
    begin
      Result := TTypeInfoCache.Instance.get(lowercase(trimName(N)));
    end;

    procedure FromDictionary(cn: IGenericClassName);
    var
      I: TSuperObjectIter;
      ov: ISuperObject;
      rt, kvt: TRttiType;
      val: Tvalue;
      kv, vv: Tvalue;
      M: TRttiMethod;
      T: TRttiInstanceType;
    begin
      rt := Context.GetType(TypeInfo);
      try
        T := rt.AsInstance;
        val := T.GetMethod('Create').Invoke(T.MetaclassType, [nil]);
        writeln(GetTypeName(val.TypeInfo));
        value := val;
        kvt := TryfindType(cn.Generics[0].ToString);
        M := rt.GetMethod('Add');
        if ObjectFindFirst(Obj, I) then
        begin
          try
            repeat
              kv := I.key;
              ov := I.val;
              if not FromJson(kvt.Handle, ov, vv) then
              begin
                value := nil;
                Result := false;
                Exit;
              end;
              M.Invoke(val, [kv, vv]);
            until not ObjectFindNext(I);
            Result := true;
          finally
            ObjectFindClose(I);
          end;
        end;
      except
        if not value.IsEmpty then
        begin
          M := rt.GetMethod('Free');
          M.Invoke(value, []);
        end;
        value := nil;
        Result := false;
      end;
    end;

    procedure FromList(cn: IGenericClassName);
    var
      I: ISuperObject;
      rt, kvt: TRttiType;
      val: Tvalue;
      kv: Tvalue;
      M: TRttiMethod;
      S: string;
      T: TRttiInstanceType;
    begin
      rt := TryfindType(cn.ToString);
      try
        T := rt.AsInstance;
        val := T.GetMethod('Create').Invoke(T.MetaclassType, []);
        writeln(GetTypeName(val.TypeInfo));
        value := val;
        kvt := TryfindType(cn.Generics[0].ToString);
        M := rt.GetMethod('Add');
        for I in Obj do
        begin
          if not FromJson(kvt.Handle, I, kv) then
          begin
            value := nil;
            Result := false;
            Exit;
          end;
          M.Invoke(val, [kv]);
        end;
        Result := true;
      except
        if not value.IsEmpty then
        begin
          M := rt.GetMethod('Free');
          M.Invoke(value, []);
        end;
        value := nil;
        Result := false;
      end;
    end;

    procedure FromClass;
    var
      F: TRttiField;
      v: Tvalue;
      cn: IGenericClassName;
    begin
      case ObjectGetType(Obj) of
        stArray:
          begin
            cn := TGenericClassName.Create(GetTypeName(TypeInfo));
            if cn.BaseType = 'tlist' then
              FromList(cn);
          end;
        stObject:
          begin
            cn := TGenericClassName.Create(GetTypeName(TypeInfo));
            if cn.BaseType = 'tdictionary' then
              FromDictionary(cn)
            else
            begin

              if value.Kind <> tkClass then
                value := GetTypeData(TypeInfo).ClassType.Create;
              for F in Context.GetType(value.AsObject.ClassType).GetFields do
                if F.FieldType <> nil then
                begin
                  v := Tvalue.Empty;
                  Result := FromJson(F.FieldType.Handle, GetFieldDefault(F, Obj.AsObject[GetFieldName(F)]), v);
                  if Result then
                    F.Setvalue(value.AsObject, v)
                  else
                    Exit;
                end;
            end;
          end;
        stNull:
          begin
            value := nil;
            Result := true;
          end
      else
        // error
        value := nil;
        Result := false;
      end;
    end;

    procedure FromRecord;
    var
      F: TRttiField;
      p: Pointer;
      v: Tvalue;
    begin
      Result := true;
      Tvalue.Make(nil, TypeInfo, value);
      for F in Context.GetType(TypeInfo).GetFields do
      begin
        if ObjectIsType(Obj, stObject) and (F.FieldType <> nil) then
        begin
{$IFDEF VER210}
          p := IvalueData(TvalueData(value).FHeapData).GetReferenceToRawData;
{$ELSE}
          p := TvalueData(value).FvalueData.GetReferenceToRawData;
{$ENDIF}
          Result := FromJson(F.FieldType.Handle, GetFieldDefault(F, Obj.AsObject[GetFieldName(F)]), v);
          if Result then
            F.Setvalue(p, v)
          else
          begin
            // Writeln(f.Name);
            Exit;
          end;
        end
        else
        begin
          Result := false;
          Exit;
        end;
      end;
    end;

    procedure FromDynArray;
    var
      I: Integer;
      p: Pointer;
      pb: PByte;
      val: Tvalue;
      typ: PTypeData;
      el: PTypeInfo;
    begin
      case ObjectGetType(Obj) of
        stArray:
          begin
            I := Obj.AsArray.Length;
            p := nil;
            DynArraySetLength(p, TypeInfo, 1, @I);
            pb := p;
            typ := GetTypeData(TypeInfo);
            if typ.elType <> nil then
              el := typ.elType^
            else
              el := typ.elType2^;

            Result := true;
            for I := 0 to I - 1 do
            begin
              Result := FromJson(el, Obj.AsArray[I], val);
              if not Result then
                Break;
              val.ExtractRawData(pb);
              val := Tvalue.Empty;
              Inc(pb, typ.elSize);
            end;
            if Result then
              Tvalue.MakeWithoutCopy(@p, TypeInfo, value)
            else
              DynArrayClear(p, TypeInfo);
          end;
        stNull:
          begin
            Tvalue.MakeWithoutCopy(nil, TypeInfo, value);
            Result := true;
          end;
      else
        I := 1;
        p := nil;
        DynArraySetLength(p, TypeInfo, 1, @I);
        pb := p;
        typ := GetTypeData(TypeInfo);
        if typ.elType <> nil then
          el := typ.elType^
        else
          el := typ.elType2^;

        Result := FromJson(el, Obj, val);
        val.ExtractRawData(pb);
        val := Tvalue.Empty;

        if Result then
          Tvalue.MakeWithoutCopy(@p, TypeInfo, value)
        else
          DynArrayClear(p, TypeInfo);
      end;
    end;

    procedure FromArray;
    var
      ArrayData: PArrayTypeData;
      idx: Integer;
      function ProcessDim(dim: byte; const O: ISuperObject): Boolean;
      var
        I: Integer;
        v: Tvalue;
        A: PTypeData;
      begin
        if ObjectIsType(O, stArray) and (ArrayData.Dims[dim - 1] <> nil) then
        begin
          A := @GetTypeData(ArrayData.Dims[dim - 1]^).ArrayData;
          if (A.Maxvalue - A.Minvalue + 1) <> O.AsArray.Length then
          begin
            Result := false;
            Exit;
          end;
          Result := true;
          if dim = ArrayData.DimCount then
            for I := A.Minvalue to A.Maxvalue do
            begin
              Result := FromJson(ArrayData.elType^, O.AsArray[I], v);
              if not Result then
                Exit;
              value.SetArrayElement(idx, v);
              Inc(idx);
            end
          else
            for I := A.Minvalue to A.Maxvalue do
            begin
              Result := ProcessDim(dim + 1, O.AsArray[I]);
              if not Result then
                Exit;
            end;
        end
        else
          Result := false;
      end;

    var
      I: Integer;
      v: Tvalue;
    begin
      Tvalue.Make(nil, TypeInfo, value);
      ArrayData := @GetTypeData(TypeInfo).ArrayData;
      idx := 0;
      if ArrayData.DimCount = 1 then
      begin
        if ObjectIsType(Obj, stArray) and (Obj.AsArray.Length = ArrayData.ElCount) then
        begin
          Result := true;
          for I := 0 to ArrayData.ElCount - 1 do
          begin
            Result := FromJson(ArrayData.elType^, Obj.AsArray[I], v);
            if not Result then
              Exit;
            value.SetArrayElement(idx, v);
            v := Tvalue.Empty;
            Inc(idx);
          end;
        end
        else
          Result := false;
      end
      else
        Result := ProcessDim(1, Obj);
    end;

    procedure FromClassRef;
    var
      r: TRttiType;
    begin
      if ObjectIsType(Obj, stString) then
      begin
        r := Context.FindType(Obj.AsString);
        if r <> nil then
        begin
          value := TRttiInstanceType(r).MetaclassType;
          Result := true;
        end
        else
          Result := false;
      end
      else
        Result := false;
    end;

    procedure FromUnknown;
    begin
      case ObjectGetType(Obj) of
        stBoolean:
          begin
            value := Obj.AsBoolean;
            Result := true;
          end;
        stDouble:
          begin
            value := Obj.AsDouble;
            Result := true;
          end;
        stCurrency:
          begin
            value := Obj.AsCurrency;
            Result := true;
          end;
        stInt:
          begin
            value := Obj.AsInteger;
            Result := true;
          end;
        stString:
          begin
            value := Obj.AsString;
            Result := true;
          end
      else
        value := nil;
        Result := false;
      end;
    end;

    procedure FromInterface;
    const
      soguid: tguid = '{4B86A9E3-E094-4E5A-954A-69048B7B6327}';
    var
      O: ISuperObject;
      aguid: tguid;
    begin
      aguid := GetTypeData(TypeInfo).guid;
      if CompareMem(@aguid, @soguid, sizeof(tguid)) then
      begin
        if Obj <> nil then
          Tvalue.Make(@Obj, TypeInfo, value)
        else
        begin
          O := TSuperObject.Create(stNull);
          Tvalue.Make(@O, TypeInfo, value);
        end;
        Result := true;
      end
      else
        Result := false;
    end;

  var
    Serial: TSerialFromJson;
  begin

    if TypeInfo <> nil then
    begin
      if not SerialFromJson.trygetvalue(TypeInfo, Serial) then
        case TypeInfo.Kind of
          tkChar:
            FromChar;
          tkInt64:
            FromInt64;
          tkEnumeration, tkInteger:
            FromInt(Obj);
          tkSet:
            fromSet;
          tkFloat:
            FromFloat(Obj);
          tkString, tkLString, tkUString, tkWString:
            FromString;
          tkClass:
            FromClass;
          tkMethod:
            ;
          tkWChar:
            FromWideChar;
          tkRecord:
            FromRecord;
          tkPointer:
            ;
          tkInterface:
            FromInterface;
          tkArray:
            FromArray;
          tkDynArray:
            FromDynArray;
          tkClassRef:
            FromClassRef;
        else
          FromUnknown
        end
      else
      begin
        Tvalue.Make(nil, TypeInfo, value);
        Result := Serial(Self, Obj, value);
      end;
    end
    else
      Result := false;
  end;

  function TSuperRttiContext.ToJson(var value: Tvalue; const index: ISuperObject): ISuperObject;
    procedure ToInt64;
    begin
      Result := TSuperObject.Create(SuperInt(value.AsInt64));
    end;

    procedure ToChar;
    begin
      Result := TSuperObject.Create(string(value.AsType<AnsiChar>));
    end;

    procedure ToInteger;
    begin
      Result := TSuperObject.Create(TvalueData(value).FAsSLong);
    end;

    procedure ToFloat;
    begin
      case value.TypeData.FloatType of
        ftSingle:
          Result := TSuperObject.Create(TvalueData(value).FAsSingle);
        ftDouble:
          Result := TSuperObject.Create(TvalueData(value).FAsDouble);
        ftExtended:
          Result := TSuperObject.Create(TvalueData(value).FAsExtended);
        ftComp:
          Result := TSuperObject.Create(TvalueData(value).FAsSInt64);
        ftCurr:
          Result := TSuperObject.CreateCurrency(TvalueData(value).FAsCurr);
      end;
    end;

    procedure ToString;
    begin
      Result := TSuperObject.Create(string(value.AsType<string>));
    end;

    procedure ToList(cn: IGenericClassName);
    var
      TypeInfo: PTypeInfo;
      rt: TRttiType;
      p: trttiproperty;
      M: TRttiMethod;
      C: Integer;
      v: Tvalue;
      I: Integer;
      Iv: Tvalue;
    begin

      TypeInfo := TvalueData(value).FtypeInfo;
      Result := TSuperObject.Create(stArray);
      rt := Context.GetType(TypeInfo);
      p := rt.GetProperty('Count');
      C := p.Getvalue(value.AsObject).AsInteger;
      M := rt.GetMethod('GetItem');
      for I := 0 to C - 1 do
      begin
        Iv := I;
        v := M.Invoke(value, [Iv]);
        Result.AsArray.Add(ToJson(v, index))
      end;
    end;

    procedure ToDictionary(cn: IGenericClassName);
    var
      TypeInfo: PTypeInfo;
      rt, et, pt: TRttiType;
      kf, vf: TRttiField;
      p: trttiproperty;
      me, F, mn: TRttiMethod;
      e, v, kv, vv: Tvalue;
    begin
      TypeInfo := TvalueData(value).FtypeInfo;
      Result := TSuperObject.Create(stObject);
      rt := Context.GetType(TypeInfo);
      // get the enumerator
      me := rt.GetMethod('GetEnumerator');
      e := me.Invoke(value, []);
      et := Context.GetType(TvalueData(e).FtypeInfo);
      try
        mn := et.GetMethod('MoveNext');
        p := et.GetProperty('Current');
        // get type of property
        pt := p.propertyType;
        kf := pt.getfield('Key');
        vf := pt.getfield('Value');
        while mn.Invoke(e, []).AsBoolean do
        begin
          // get the pair
          v := p.Getvalue(e.AsObject);
          kv := kf.Getvalue(v.GetReferenceToRawData);
          vv := vf.Getvalue(v.GetReferenceToRawData);
          Result.AsObject[kv.ToString] := ToJson(vv, index);
        end;
      finally
        // free the enumerator
        et := Context.GetType(TvalueData(e).FtypeInfo);
        F := et.GetMethod('Free');
        F.Invoke(e, []);
      end;
    end;

    procedure ToClass;
    var
      O: ISuperObject;
      F: TRttiField;
      v: Tvalue;
      cn: IGenericClassName;
    begin
      if TvalueData(value).FAsObject <> nil then
      begin
        cn := TGenericClassName.Create(GetTypeName(TvalueData(value).FtypeInfo));
        if cn.BaseType = 'tdictionary' then
          ToDictionary(cn)
        else if cn.BaseType = 'tlist' then
          ToList(cn)
        else
        begin
          O := index[IntToStr(NativeInt(value.AsObject))];
          if O = nil then
          begin
            Result := TSuperObject.Create(stObject);
            index[IntToStr(NativeInt(value.AsObject))] := Result;
            for F in Context.GetType(value.AsObject.ClassType).GetFields do
              if F.FieldType <> nil then
              begin
                v := F.Getvalue(value.AsObject);
                Result.AsObject[GetFieldName(F)] := ToJson(v, index);
              end
          end
          else
            Result := O;
        end;
      end
      else
        Result := nil;
    end;

    procedure ToWChar;
    begin
      Result := TSuperObject.Create(string(value.AsType<WideChar>));
    end;

    procedure ToVariant;
    begin
      Result := SO(value.AsVariant);
    end;

    procedure ToRecord;
    var
      F: TRttiField;
      v: Tvalue;
    begin
      Result := TSuperObject.Create(stObject);
      for F in Context.GetType(value.TypeInfo).GetFields do
      begin
{$IFDEF VER210}
        v := F.Getvalue(IvalueData(TvalueData(value).FHeapData).GetReferenceToRawData);
{$ELSE}
        v := F.Getvalue(TvalueData(value).FvalueData.GetReferenceToRawData);
{$ENDIF}
        Result.AsObject[GetFieldName(F)] := ToJson(v, index);
      end;
    end;

    procedure ToArray;
    var
      idx: Integer;
      ArrayData: PArrayTypeData;

      procedure ProcessDim(dim: byte; const O: ISuperObject);
      var
        dt: PTypeData;
        I: Integer;
        o2: ISuperObject;
        v: Tvalue;
      begin
        if ArrayData.Dims[dim - 1] = nil then
          Exit;
        dt := GetTypeData(ArrayData.Dims[dim - 1]^);
        if dim = ArrayData.DimCount then
          for I := dt.Minvalue to dt.Maxvalue do
          begin
            v := value.GetArrayElement(idx);
            O.AsArray.Add(ToJson(v, index));
            Inc(idx);
          end
        else
          for I := dt.Minvalue to dt.Maxvalue do
          begin
            o2 := TSuperObject.Create(stArray);
            O.AsArray.Add(o2);
            ProcessDim(dim + 1, o2);
          end;
      end;

    var
      I: Integer;
      v: Tvalue;
    begin
      Result := TSuperObject.Create(stArray);
      ArrayData := @value.TypeData.ArrayData;
      idx := 0;
      if ArrayData.DimCount = 1 then
        for I := 0 to ArrayData.ElCount - 1 do
        begin
          v := value.GetArrayElement(I);
          Result.AsArray.Add(ToJson(v, index))
        end
      else
        ProcessDim(1, Result);
    end;

    procedure ToDynArray;
    var
      I: Integer;
      v: Tvalue;
    begin
      Result := TSuperObject.Create(stArray);
      for I := 0 to value.GetArrayLength - 1 do
      begin
        v := value.GetArrayElement(I);
        Result.AsArray.Add(ToJson(v, index));
      end;
    end;

    procedure ToClassRef;
    begin
      if TvalueData(value).FAsClass <> nil then
        Result := TSuperObject.Create(string(TvalueData(value).FAsClass.UnitName + '.' + TvalueData(value).FAsClass.ClassName))
      else
        Result := nil;
    end;

    procedure ToInterface;
{$IFNDEF VER210}
    var
      intf: IInterface;
{$ENDIF}
    begin
{$IFDEF VER210}
      if TvalueData(value).FHeapData <> nil then
        TvalueData(value).FHeapData.QueryInterface(ISuperObject, Result)
      else
        Result := nil;
{$ELSE}
      if TvalueData(value).FvalueData <> nil then
      begin
        intf := IInterface(PPointer(TvalueData(value).FvalueData.GetReferenceToRawData)^);
        if intf <> nil then
          intf.QueryInterface(ISuperObject, Result)
        else
          Result := nil;
      end
      else
        Result := nil;
{$ENDIF}
    end;

  var
    Serial: TSerialToJson;
  begin
    if not SerialToJson.trygetvalue(value.TypeInfo, Serial) then
      case value.Kind of
        tkInt64:
          ToInt64;
        tkChar:
          ToChar;
        tkSet, tkInteger, tkEnumeration:
          ToInteger;
        tkFloat:
          ToFloat;
        tkString, tkLString, tkUString, tkWString:
          ToString;
        tkClass:
          ToClass;
        tkWChar:
          ToWChar;
        tkVariant:
          ToVariant;
        tkRecord:
          ToRecord;
        tkArray:
          ToArray;
        tkDynArray:
          ToDynArray;
        tkClassRef:
          ToClassRef;
        tkInterface:
          ToInterface;
      else
        Result := nil;
      end
    else
      Result := Serial(Self, value, index);
  end;

  { TSuperObjectHelper }

  constructor TSuperObjectHelper.FromJson(const Obj: ISuperObject; ctx: TSuperRttiContext = nil);
  var
    v: Tvalue;
    ctxowned: Boolean;
  begin
    if ctx = nil then
    begin
      ctx := TSuperRttiContext.Create;
      ctxowned := true;
    end
    else
      ctxowned := false;
    try
      v := Self;
      if not ctx.FromJson(v.TypeInfo, Obj, v) then
        raise Exception.Create('Invalid object');
    finally
      if ctxowned then
        ctx.free;
    end;
  end;

  constructor TSuperObjectHelper.FromJson(const str: string; ctx: TSuperRttiContext = nil);
  begin
    FromJson(SO(str), ctx);
  end;

  function TSuperObjectHelper.ToJson(ctx: TSuperRttiContext = nil): ISuperObject;
  var
    v: Tvalue;
    ctxowned: Boolean;
  begin
    if ctx = nil then
    begin
      ctx := TSuperRttiContext.Create;
      ctxowned := true;
    end
    else
      ctxowned := false;
    try
      v := Self;
      Result := ctx.ToJson(v, SO);
    finally
      if ctxowned then
        ctx.free;
    end;
  end;

{$ENDIF}
  { TGenericClassName }

  constructor TGenericClassName.Create(typ: string);

    function extractGenerics(items: string): TList<IGenericClassName>;

    var
      I: Integer;
      B: string;
    begin
      Result := TList<IGenericClassName>.Create();
      while Length(items) > 0 do
      begin
        I := pos(',', items);
        if I = 0 then
        begin
          B := items;
          items := '';
        end
        else
        begin
          B := Copy(items, 1, I - 1);
          items := Copy(items, I + 1);
        end;
        Result.Add(TGenericClassName.Create(B));
      end;
    end;

  var
    I: Integer;
  begin
    I := pos('<', typ);
    if I > 0 then
    begin
      // generic
      FBaseType := lowercase(Copy(typ, 1, I - 1));
      FGenerics := extractGenerics(Copy(typ, I + 1, Length(typ) - 1 - I));
    end
    else
      FBaseType := typ;
  end;

  destructor TGenericClassName.Destroy;
  begin
    FGenerics.free;
    inherited;
  end;

  function TGenericClassName.ToString: string;
  var
    I: Integer;
    cn: IGenericClassName;
  begin
    Result := FBaseType;
    if IsGeneric then
    begin
      Result := Result + '<';
      I := 0;
      for cn in Generics do
      begin
        if I > 0 then
          Result := Result + ',';
        Result := Result + cn.ToString;
        Inc(I);
      end;
      Result := Result + '>';
    end;
  end;

  function TGenericClassName.GetBaseType: string;
  begin
    Result := FBaseType;
  end;

  function TGenericClassName.GetGenerics: TList<IGenericClassName>;
  begin
    Result := FGenerics;
  end;

  function TGenericClassName.GetIsGeneric: Boolean;
  begin
    Result := FGenerics <> nil;
  end;

{$IFDEF DEBUG}

initialization

finalization

assert(debugcount = 0, 'Memory leak');
{$ENDIF}

end.
