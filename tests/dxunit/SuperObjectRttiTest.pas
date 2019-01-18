unit SuperObjectRttiTest;

interface

uses
  DUnitX.TestFramework,
  System.Generics.Collections,
  System.TypInfo,
  superobject;

type

  [TestFixture]
  TSuperObjectRttiTest = class(TObject)
  public
    [Test]
    procedure BasicTest;

    [Test]
    procedure DictionaryTest;

    [Test]
    procedure ParseGenericTest;

    [Test]
    procedure ListTest;

    [Test]
    procedure ArrayTest;
  end;

implementation

procedure TSuperObjectRttiTest.BasicTest;
type
  TContact = record
    email: string;
    phoneno: string;
  end;

  TPerson = record
    firstname: string;
    lastname: string;
    contact: TContact;
  end;
var
  ctx: TSuperRttiContext;
  response: ISuperObject;
  person: TPerson;
begin
  ctx := TSuperRttiContext.Create;
  try
    response := SO('{ "firstname": "conrad", "lastname" : "vermeulen", "contact" : { "email": "test@example.com", "phoneno" : "1234" } }');
    Assert.AreEqual('conrad', response.S['firstname']);
    Assert.AreEqual('vermeulen', response.S['lastname']);

    person := ctx.AsType<TPerson>(response);
    Assert.AreEqual('conrad', person.firstname);
    Assert.AreEqual('vermeulen', person.lastname);
    Assert.AreEqual('test@example.com', person.contact.email);
    Assert.AreEqual('1234', person.contact.phoneno);
  finally
    ctx.Free;
  end;
end;

procedure TSuperObjectRttiTest.DictionaryTest;
var
  ctx: TSuperRttiContext;
  response: ISuperObject;
  D: TDictionary<string, String>;
  ti: pointer;
  S: string;
begin
  ctx := TSuperRttiContext.Create;
  try
    response := SO('{ "firstname": "conrad", "lastname" : "vermeulen" }');
    D := ctx.AsType < TDictionary < string, String >> (response);
    Assert.IsTrue(D.ContainsKey('firstname'));
    Assert.IsTrue(D.ContainsKey('lastname'));
    Assert.AreEqual('conrad', D['firstname']);
    Assert.AreEqual('vermeulen', D['lastname']);
    response := ctx.AsJSon < TDictionary < string, String >> (D);
    S := response.asstring;
    Assert.AreEqual('{"firstname":"conrad","lastname":"vermeulen"}', S);
    D.Free;

  finally
    ctx.Free;
  end;
end;

procedure TSuperObjectRttiTest.ListTest;
var
  ctx: TSuperRttiContext;
  response: ISuperObject;
  D: Tlist<string>;
  ti: pointer;
  S: string;
begin
  ctx := TSuperRttiContext.Create;
  try
    response := SO('[ "firstname", "conrad", "lastname" , "vermeulen" ]');

    D := ctx.AsType < Tlist < string >> (response);
    Assert.AreEqual(4, D.Count);
    Assert.AreEqual('firstname', D.Items[0]);
    Assert.AreEqual('conrad', D.Items[1]);
    Assert.AreEqual('lastname', D.Items[2]);
    Assert.AreEqual('vermeulen', D.Items[3]);
    response := ctx.AsJSon < Tlist < string >> (D);
    S := response.asstring;
    Assert.AreEqual('["firstname","conrad","lastname","vermeulen"]', S);
    D.Free;
  finally
    ctx.Free;
  end;
end;

procedure TSuperObjectRttiTest.ArrayTest;
var
  ctx: TSuperRttiContext;
  response: ISuperObject;
  D: tarray<string>;
  ti: pointer;
  S: string;
begin
  ctx := TSuperRttiContext.Create;
  try
    response := SO('[ "firstname", "conrad", "lastname" , "vermeulen" ]');
    D := ctx.AsType < tarray < string >> (response);
    response := ctx.AsJSon < tarray < string >> (D);
    S := response.asstring;
    Assert.AreEqual('["firstname","conrad","lastname","vermeulen"]', S);
  finally
    ctx.Free;
  end;
end;

procedure TSuperObjectRttiTest.ParseGenericTest;
var
  cn: IGenericClassName;
begin
  cn := TGenericClassName.Create('TDictionary<string,TList<integer>>');
  Assert.AreEqual('TDictionary', cn.BaseType);
  Assert.AreEqual('string', cn.Generics[0].BaseType);
  Assert.AreEqual('TList', cn.Generics[1].BaseType);
  Assert.AreEqual('integer', cn.Generics[1].Generics[0].BaseType);
end;

initialization

ReportMemoryLeaksOnShutdown := DebugHook <> 0;
TDUnitX.RegisterTestFixture(TSuperObjectRttiTest);

finalization

end.
