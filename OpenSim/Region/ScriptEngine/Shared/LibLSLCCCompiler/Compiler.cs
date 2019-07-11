/*
 * Copyright (c) Contributors, http://opensimulator.org/
 * See CONTRIBUTORS.TXT for a full list of copyright holders.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the OpenSimulator Project nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE DEVELOPERS ``AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE CONTRIBUTORS BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


using System;
using System.CodeDom.Compiler;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading;
using System.Xml;
using log4net;
using LibLSLCC.CodeValidator;
using LibLSLCC.Compilers;
using LibLSLCC.CSharp;
using LibLSLCC.LibraryData;
using LibLSLCC.LibraryData.Reflection;
using Microsoft.CSharp;
using Microsoft.VisualBasic;
using Nini.Config;
using OpenMetaverse;
using OpenSim.Framework;
using OpenSim.Region.Framework.Interfaces;
using OpenSim.Region.ScriptEngine.Interfaces;
using OpenSim.Region.ScriptEngine.Shared.CodeTools;
using OpenSim.Region.ScriptEngine.Shared.ScriptBase;

namespace OpenSim.Region.ScriptEngine.Shared.LibLSLCCCompiler
{
    public class Compiler : ICompiler
    {
        private const string LogHeader = "[LibLSLCC]:";

        private static readonly ILog m_log = LogManager.GetLogger(MethodBase.GetCurrentMethod().DeclaringType);


        private LSLLibraryDataProvider _libraryDataProvider;

        internal enum CompileLanguage
        {
            lsl = 0,
            cs = 1,
            vb = 2,
            csraw = 3,
            vbraw = 4
        }


        private CompileLanguage DefaultCompileLanguage;
        private bool WriteScriptSourceToDebugFile;
        private bool CompileWithDebugInformation;

        private readonly Dictionary<string, bool> AllowedCompilers =
            new Dictionary<string, bool>(StringComparer.CurrentCultureIgnoreCase);

        private readonly Dictionary<string, CompileLanguage> LanguageMapping =
            new Dictionary<string, CompileLanguage>(StringComparer.CurrentCultureIgnoreCase);

        private bool m_insertCoopTerminationCalls;

        private string FilePrefix;

        private readonly string ScriptEnginesPath;


        private ICodeConverter LSL_Converter;

        private readonly List<string> m_warnings = new List<string>();


        private static readonly CSharpCodeProvider CScodeProvider = new CSharpCodeProvider();
        private static readonly VBCodeProvider VBcodeProvider = new VBCodeProvider();


        private readonly IScriptEngine m_scriptEngine;

        private bool in_startup = true;

        private bool EnableCompilerWarnings;
        private bool CreateClassWrapperForCSharpScripts;
        private bool CreateClassWrapperForVBScripts;


        public Compiler(IScriptEngine scriptEngine)
        {
            m_scriptEngine = scriptEngine;
            ScriptEnginesPath = scriptEngine.ScriptEnginePath;

            InitLibraryData();
            ReadConfig();

            SetupCommands();
        }



        private void SetupCommands()
        {
            MainConsole.Instance.Commands.AddCommand("Scripts", false,
                "liblslcc write_library_xml",
                "liblslcc write_library_xml [<file>]",
                "Write LibLSLCC library data to an XML file.",
                "Write library data collected from OpenSim and its loaded modules to an XML file " + Environment.NewLine +
                "in LibLSLCC Library Data format.  The file will be overwritten if it exists. " + Environment.NewLine +
                "The produced file is LE - UTF-16 encoded.",
                DumpLibraryData);
        }



        private void DumpLibraryData(string module, string[] cmd)
        {
            if (cmd.Length < 3)
            {
                m_log.Error(LogHeader + " No file was specified, you must specify a file to write the library data to.");
                return;
            }
            try
            {
                string file = cmd[2];

                using (
                    var writer = new XmlTextWriter(File.Create(file), Encoding.Unicode)
                    {
                        Formatting = Formatting.Indented
                    })
                {
                    LSLLibraryDataXmlSerializer.WriteXml(_libraryDataProvider, writer);
                }

                m_log.InfoFormat(LogHeader + " Successfully wrote LibLSLCC Library data to: \"{0}\".",
                    Path.GetFullPath(file));
            }
            catch (Exception err)
            {
                m_log.ErrorFormat(LogHeader + " Issue writing to library data file, reason: \"{0}\"", err.Message);
            }
        }



        private class ScriptBaseClassConstantValueStringConverter : ILSLValueStringConverter
        {
            private bool Convert(MemberInfo member, Type declarationType, LSLType constantType, object fieldValue, out string valueString)
            {
                Type type = fieldValue.GetType();

                if (type == typeof(LSL_Types.list))
                {
                    m_log.WarnFormat(
                        LogHeader + " {0} constant '{1}' is an LSL_Type.list and not currently supported by the compiler," +
                        " '{1}' will be left undefined.", 
                        member.DeclaringType.Name, 
                        member.Name);

                    valueString = null;
                    return false;

                }
                if (type.IsArray)
                {
                    m_log.WarnFormat(
                        LogHeader + " {0} constant '{1}' is an Array of '{2}' and not currently supported by the compiler," +
                        " '{1}' will be left undefined.",
                        member.DeclaringType.Name,
                        member.Name, 
                        type.GetElementType());

                    valueString = null;
                    return false;
                }

                //every types ToString() should be successfully parsed by LibLSLCC's LSLLibraryConstantSignature
                //we should still check this.
                var str = fieldValue.ToString();

                if (LSLLibraryConstantSignature.ValidateValueString(constantType, str))
                {
                    valueString = str;
                    return true;
                }

                m_log.WarnFormat(
                        LogHeader + " {0} constant '{1}' declared with type '{2}' has the value '{3}' whose " +
                        "string representation cannot be parsed by LSLLibraryConstantSignature.ValueString," +
                        " '{1}' will be left undefined.",
                        member.DeclaringType.Name, 
                        member.Name, 
                        declarationType.Name,
                        fieldValue);

                valueString = null;
                return false;

            }

            public bool ConvertProperty(PropertyInfo propertyInfo, LSLType constantType, object fieldValue, out string valueString)
            {
                return Convert(propertyInfo, propertyInfo.PropertyType, constantType, fieldValue, out valueString);
            }

            public bool ConvertField(FieldInfo fieldInfo, LSLType constantType, object fieldValue, out string valueString)
            {
                return Convert(fieldInfo, fieldInfo.FieldType, constantType, fieldValue, out valueString);
            }
        }



        private class ScriptBaseClassTypeConverter : ILSLConstantTypeConverter, ILSLReturnTypeConverter,
            ILSLParamTypeConverter
        {
            public static readonly Dictionary<Type, LSLType> TypeMappingsCommon = new Dictionary<Type, LSLType>
            {
                {typeof (string), LSLType.String},
                {typeof (LSL_Types.LSLString), LSLType.String},
                {typeof (bool), LSLType.Integer},
                {typeof (short), LSLType.Integer},
                {typeof (int), LSLType.Integer},
                {typeof (long), LSLType.Integer},
                {typeof (ushort), LSLType.Integer},
                {typeof (uint), LSLType.Integer},
                {typeof (ulong), LSLType.Integer},
                {typeof (LSL_Types.LSLInteger), LSLType.Integer},
                {typeof (double), LSLType.Float},
                {typeof (float), LSLType.Float},
                {typeof (LSL_Types.LSLFloat), LSLType.Float},
                {typeof (object[]), LSLType.List},
                {typeof (LSL_Types.list), LSLType.List},
                {typeof (LSL_Types.key), LSLType.Key},
                {typeof (UUID), LSLType.Key},
                {typeof (LSL_Types.Quaternion), LSLType.Rotation},
                {typeof (Quaternion), LSLType.Rotation},
                {typeof (Vector4), LSLType.Rotation},
                {typeof (LSL_Types.Vector3), LSLType.Vector},
                {typeof (Vector3), LSLType.Vector},
                {typeof (Vector3d), LSLType.Vector}
            };


            public static readonly Dictionary<Type, LSLType> ConstantMappings =
                new Dictionary<Type, LSLType>(TypeMappingsCommon);


            public static readonly Dictionary<Type, LSLType> ReturnMappings =
                new Dictionary<Type, LSLType>(TypeMappingsCommon)
                {
                    {typeof (void), LSLType.Void}
                };

            public static readonly Dictionary<Type, LSLType> ParameterMappings =
                new Dictionary<Type, LSLType>(TypeMappingsCommon)
                {
                    //an exception will be thrown if the parameter is not variadic
                    {typeof (object), LSLType.Void}
                };


            private bool ConvertConstant(MemberInfo member, Type inType, out LSLType outType)
            {
                LSLType o;
                if (ConstantMappings.TryGetValue(inType, out o))
                {
                    outType = o;
                    return true;
                }

                var propInfo = member as PropertyInfo;
                var fieldInfo = member as FieldInfo;

                Type type = propInfo != null ? propInfo.PropertyType : fieldInfo.FieldType;

                m_log.WarnFormat(
                    LogHeader +  
                    " Constant '{0}' has an un-mappable declaration type '{1}'," +
                    " '{0}' will be left undefined.",
                    member.Name, type.Name);

                outType = LSLType.Void;
                return false;
            }

            public bool ConvertField(FieldInfo fieldInfo, out LSLType outType)
            {
                return ConvertConstant(fieldInfo, fieldInfo.FieldType, out outType);
            }

            public bool ConvertProperty(PropertyInfo fieldInfo, out LSLType outType)
            {
                return ConvertConstant(fieldInfo, fieldInfo.PropertyType, out outType);
            }

            public bool ConvertReturn(MethodInfo methodInfo, out LSLType outType)
            {
                LSLType o;
                if (ReturnMappings.TryGetValue(methodInfo.ReturnType, out o))
                {
                    outType = o;
                    return true;
                }

                m_log.WarnFormat(
                    LogHeader +
                    " Return type of reflected script method '{0}' uses and un-mappable return type '{1}'," +
                    " '{0}' be left undefined.",
                    methodInfo.Name, methodInfo.ReturnType.Name);

                outType = LSLType.Void;
                return false;
            }

            public bool ConvertParameter(ParameterInfo parameterInfo, Type basicType, out LSLType outType)
            {
                LSLType o;
                if (ParameterMappings.TryGetValue(basicType, out o))
                {
                    outType = o;
                    return true;
                }

                m_log.WarnFormat(
                    LogHeader +
                    " Parameter '{0}' of reflected script method '{1}' uses and un-mappable type '{2}'," +
                    " '{1}' be left undefined.",
                    parameterInfo.Name, 
                    parameterInfo.Member.Name,
                    parameterInfo.ParameterType.Name);

                outType = LSLType.Void;
                return false;
            }
        }


        private class ScriptBaseClassMethodFilter : ILSLMethodFilter
        {
            private static readonly HashSet<string> MethodBlacklist = new HashSet<string>
            {
                //ignore implementation detail of ScriptBaseClass.
                //some of these have valid mappings to LSL signatures.
                //
                //we do not want those that can actually map into LSL signatures being
                //called by from compiled LSL scripts.
                "InitializeLifetimeService",
                "GetStateEventFlags",
                "Close",
                "GetApis",
                "GetVars",
                "SetVars",
                "InitApi",
                "StateChange",
                "ResetVars",
                "NoOp",

                //=======
                //just to make things clear, osParseJSON and osParseJSONNew will be ignored
                //regardless of whether or not they are in this black list.
                //
                //there is no conversion for their return type, and the LibLSLCC class serializer
                //is setup in this compiler to just ignore them and not throw an exception when they
                //are encountered.
                //
                "osParseJSON",
                "osParseJSONNew"
            };

            public bool PreFilter(LSLLibraryDataReflectionSerializer serializer, MethodInfo info)
            {
                return info.Name.StartsWith("ApiType") || MethodBlacklist.Contains(info.Name);
            }

            public bool MutateSignature(LSLLibraryDataReflectionSerializer serializer, MethodInfo info,
                LSLLibraryFunctionSignature signature)
            {
                return false;
            }
        }


        private class ScriptBaseClassConstantFilter : ILSLConstantFilter
        {
            private static readonly HashSet<string> ConstantBlacklist = new HashSet<string>
            {
                //Only present in debug builds
                "GCDummy"
            };

            public bool PreFilter(LSLLibraryDataReflectionSerializer serializer, PropertyInfo info)
            {
                return ConstantBlacklist.Contains(info.Name);
            }

            public bool PreFilter(LSLLibraryDataReflectionSerializer serializer, FieldInfo info)
            {
                return ConstantBlacklist.Contains(info.Name);
            }

            public bool MutateSignature(LSLLibraryDataReflectionSerializer serializer, PropertyInfo info,
                LSLLibraryConstantSignature signature)
            {
                return false;
            }

            public bool MutateSignature(LSLLibraryDataReflectionSerializer serializer, FieldInfo info,
                LSLLibraryConstantSignature signature)
            {
                return false;
            }
        }



        private bool ConvertModuleConstantType(object value, out LSLType outType)
        {
            if (value == null)
            {
                outType = LSLType.Void;
                return false;
            }

            var type = value.GetType();
            LSLType o;
            if (ScriptBaseClassTypeConverter.ConstantMappings.TryGetValue(type, out o))
            {
                outType = o;
                return true;
            }

            outType = LSLType.Void;
            return false;
        }


        private bool ConvertModuleConstantToSignature(string name, object value, out LSLLibraryConstantSignature result)
        {
            var type = value.GetType();
            LSLType lslType;


            if (type == typeof(LSL_Types.list))
            {
                m_log.WarnFormat(
                    LogHeader + " Module constant '{0}' is an LSL_Type.list and not currently supported by the compiler," +
                    " '{0}' will be left undefined.", name);

                result = null;
                return false;

            }
            if (type.IsArray)
            {
                m_log.WarnFormat(
                    LogHeader + " Module constant '{0}' is an Array of '{1}' and not currently supported by the compiler," +
                    "  '{0}' will be left undefined.", 
                    name, type.GetElementType());

                result = null;
                return false;
            }

            if (!ConvertModuleConstantType(value, out lslType))
            {
                m_log.WarnFormat(
                    LogHeader + " Module constant '{0}' has a declaration type '{1}' that is not convert-able by the compiler," +
                    " '{0}' will be left undefined.",
                    name, type.Name);

                result = null;
                return false;
            }


            var valueString = value.ToString();


            if (!LSLConstantSignature.ValidateValueString(lslType, valueString))
            {
                m_log.WarnFormat(
                    LogHeader + 
                    " Module constant '{0}' of type '{1}' has a string value of '{2}' that is not parsable"
                    + " by LSLLibraryConstantSignature.ValueString, '{0}' will be left undefined.",
                    name, type.Name, valueString);

                result = null;
                return false;
            }

            result = new LSLLibraryConstantSignature(lslType, name, valueString);
            return true;
        }


        private static readonly string EmbeddedEventDataPath =
            "OpenSim.Region.ScriptEngine.Shared.LibLSLCCCompiler.Resources.LSLEventHandlers.xml";



        private static Stream GetEmbeddedLibraryEventDataStream()
        {
            return typeof(Compiler).Assembly.GetManifestResourceStream(EmbeddedEventDataPath);
        }



        private LSLXmlLibraryDataProvider GetEmbeddedLibraryEventData()
        {
            var provider = new LSLXmlLibraryDataProvider(new [] {"os-Events"}, false);

            using (var libraryData = GetEmbeddedLibraryEventDataStream())
            {
                if (libraryData == null)
                {
                    throw new InvalidOperationException(
                        "Could not locate/open manifest resource "+ EmbeddedEventDataPath);
                }

                var reader = new XmlTextReader(libraryData);

                provider.FillFromXml(reader);
            }

            return provider;
        }


        private void InitLibraryData()
        {
            var comms = m_scriptEngine.World.RequestModuleInterface<IScriptModuleComms>();


            var commsMethods = comms.GetScriptInvocationList().Select(x => x.Method).ToList();

            var moduleSubsets =
                commsMethods.Select(x => "os-" + x.DeclaringType.Name)
                    .Distinct().ToList();


            _libraryDataProvider = new LSLLibraryDataProvider(
                new[] {"os-ScriptBaseClass", "os-Events", "os-ModuleConstants"}
                    .Concat(moduleSubsets).ToArray(), false);


            //this subset is for everything reflected from OpenSims script base class.
            _libraryDataProvider.AddSubsetDescription(
                new LSLLibrarySubsetDescription("os-ScriptBaseClass", "Reflected From ScriptBaseClass"));


            //this subset is for constants defined by modules that contain script constants.
            _libraryDataProvider.AddSubsetDescription(
                new LSLLibrarySubsetDescription("os-ModuleConstants", "Registered module constants"));


            //events are provided by LibLSLCC's embedded library data
            _libraryDataProvider.AddSubsetDescription(
                new LSLLibrarySubsetDescription("os-Events", "OpenSim event data provided by LibLSLCC"));


            foreach (var moduleSubset in moduleSubsets)
            {
                _libraryDataProvider.AddSubsetDescription(
                    new LSLLibrarySubsetDescription(moduleSubset,
                        string.Format("Registered in module {0}", moduleSubset.Substring(3))));
            }


            var reflectionSerializer = new LSLLibraryDataReflectionSerializer();


            //Allow everything to serialize, since the script base class and module classes are 
            //not attributed with LibLSLCC attributes.
            reflectionSerializer.AttributedConstantsOnly = false;
            reflectionSerializer.AttributedMethodsOnly = false;
            reflectionSerializer.AttributedParametersOnly = false;


            //Prevent serialization exceptions in these occurrences.
            //Warnings are issued to the console and the constant is left undefined if these apply.
            reflectionSerializer.FilterConstantsWithUnmappedTypes = true;
            reflectionSerializer.FilterValueStringConversionFailures = true;
            reflectionSerializer.FilterInvalidValueStrings = true;


            //Also prevent serialization exceptions in these occurrences.
            //Warnings are issued to the console and the script method is left undefined if these apply.
            reflectionSerializer.FilterMethodsWithUnmappedReturnTypes = true;
            reflectionSerializer.FilterMethodsWithUnmappedParamTypes = true;



            


            ///////////////////////////////////////
            /////// Load ScriptBaseClass Info /////
            ///////////////////////////////////////


            reflectionSerializer.FieldBindingFlags = BindingFlags.Public | BindingFlags.Static |
                                                     BindingFlags.DeclaredOnly;

            reflectionSerializer.PropertyBindingFlags = BindingFlags.Public | BindingFlags.Static |
                                                        BindingFlags.DeclaredOnly;

            reflectionSerializer.MethodBindingFlags = BindingFlags.Public | BindingFlags.Instance |
                                                      BindingFlags.DeclaredOnly;


            //Set the value string converter for constants, which converts the constant's value
            //into a string that can be assigned to LSLLibraryConstantSignature.ValueString
            reflectionSerializer.ValueStringConverter = new ScriptBaseClassConstantValueStringConverter();


            //The type converter that converts CSharp types in field declarations, method return types,
            //and method parameter types.  It implements all three reflection type converter interfaces from LibLSLCC.
            var scriptBaseClassConverter = new ScriptBaseClassTypeConverter();

            reflectionSerializer.ReturnTypeConverter = scriptBaseClassConverter;
            reflectionSerializer.ParamTypeConverter = scriptBaseClassConverter;
            reflectionSerializer.ConstantTypeConverter = scriptBaseClassConverter;


            var constantFilter = new LSLLambdaConstantFilter();

            //we want to pre-filter out any class properties, since they are not used to define
            //OpenSim script constants at the moment.
            constantFilter.PreFilterPropertyConstant = (serializer, info) => true;

            //set the constant filter to the one we just created above.
            reflectionSerializer.ConstantFilter = constantFilter;


            //These method and constant filters are for filtering
            //certain methods/constants out of the script base class which we do not want
            //defined inside LSL.  They are not used in the module loading process because
            //IScriptModuleComms guarantees that we only reflect constants/methods that are registered
            //with the module and intended to be used from LSL.
            reflectionSerializer.MethodFilter = new ScriptBaseClassMethodFilter();
            reflectionSerializer.ConstantFilter = new ScriptBaseClassConstantFilter();


            foreach (var method in reflectionSerializer.DeSerializeMethods(typeof (ScriptBaseClass)))
            {
                try
                {
                    method.Subsets.Add("os-ScriptBaseClass");
                    _libraryDataProvider.DefineFunction(method);
                }
                catch (LSLDuplicateSignatureException)
                {
                    //Some of OpenSim's script base class API functions have overloads that will
                    //map to a duplicate LSL signature, just ignore the duplicates.
                    //
                    //The first overload signature found is an accurate representation of the LSL signature.
                    //It will not cause problems with syntax checking or code generation.
                    //
                    //The overload will be resolved correctly in generated code.  The overload that accepts
                    //runtime type parameters will be preferred over the one that accepts basic CSharp parameters,
                    //since that is what the compiler uses to box it's types (Literal or Otherwise).
                }
            }


            //define the constants from the script base class
            foreach (var method in reflectionSerializer.DeSerializeConstants(typeof (ScriptBaseClass)))
            {
                method.Subsets.Add("os-ScriptBaseClass");
                _libraryDataProvider.DefineConstant(method);
            }


            //clean up settings for the module loading pass
            reflectionSerializer.ConstantFilter = null;
            reflectionSerializer.MethodFilter = null;
            reflectionSerializer.ValueStringConverter = null;



            ///////////////////////////////
            /////// Load Modules Info /////
            ///////////////////////////////
   

            //Reflection bindings for modules should be a bit different, since the module can
            //register private functions.  The field and property binding flags are not really
            //used in this pass, since IScriptModuleComms cannot provide us will FieldInfo or PropertyInfo
            //objects to serialize from.  I am still setting them here for consistency.
            reflectionSerializer.FieldBindingFlags |= BindingFlags.NonPublic | BindingFlags.Instance;
            reflectionSerializer.PropertyBindingFlags |= BindingFlags.NonPublic | BindingFlags.Instance;
            reflectionSerializer.MethodBindingFlags |= BindingFlags.NonPublic;


            //we need to tell the serializer to discard the first two parameters in registered
            //module functions, since modInvoke fills them out.
            reflectionSerializer.ParameterFilter = parameterInfo => parameterInfo.Position < 2;


            //loop through the registered module functions retrieved at the top
            //of this function.
            foreach (var method in commsMethods)
            {
                var def = reflectionSerializer.DeSerializeMethod(method);

                if (def != null)
                {
                    var sigExists = _libraryDataProvider.GetLibraryFunctionSignature(def);

                    if (sigExists != null)
                    {
                        if (sigExists.Subsets.Contains("os-ScriptBaseClass"))
                        {
                            //if the existing signature is in the 'os-ScriptBaseClass' subset,
                            //we know that the previous definition was reflected from the script base class
                            //because we put all methods reflected from there into the 'os-ScriptBaseClass' subset.

                            //this is an error on the module writers part and should not be allowed.

                            throw new Exception(
                                LogHeader +
                                string.Format(
                                    " Module function '{0}' in module type '{1}' has a duplicate definition in ScriptBaseClass!",
                                    sigExists, method.DeclaringType.Name));
                        }

                        //it's an overload that maps to the same signature types, and its already defined as MOD-Invoke
                        //just skip redeclaring it because the current signature will work.
                    }
                    else
                    {
                        string subsetName = "os-" + method.DeclaringType.Name;

                        //To make sure it does not get filtered by the library data provider when it is added,
                        //the signature needs to be given the correct subset
                        def.Subsets.Add(subsetName);

                        //This is a registered module method, so it needs to have a modInvoke* call generated for it
                        def.ModInvoke = true;

                        _libraryDataProvider.DefineFunction(def);
                    }
                }
                else
                {
                    //The method was registered with IScriptModuleComms, but it was filtered out because its return 
                    //type or one of it's parameter type's could not be converted by the class serializer into a corresponding 
                    //LibLSLCC LSLType.

                    m_log.WarnFormat(LogHeader +
                        " Failed to map OpenSim runtime types used in script method '{0}' of module '{1}', '{0}' will be left undefined!",
                        method.Name, method.DeclaringType.Name);
                }
            }


            //Remove it just because.  It's not really going to be used again.
            reflectionSerializer.ParameterFilter = null;


            //Loop through registered module constants from IScriptModuleComms
            foreach (var constant in comms.GetConstants())
            {
                if (constant.Value == null)
                {
                    //ScriptModuleCommsModule currently allows for null constants, unsure why.
                    //LibLSLCC does not support this.

                    m_log.WarnFormat(
                        LogHeader + " Module constant '{0}' is null, '{0}' will be left undefined." +
                        "  module name un-reportable!", constant.Key);
                    

                    continue;
                }


                LSLLibraryConstantSignature def;

                if (!ConvertModuleConstantToSignature(constant.Key, constant.Value, out def))
                {
                    //Skip over constants with declaration types that are not convertible to a LibLSLCC LSLType,
                    //or have ValueStrings that are not parsable by LibLSLCC's LSLLibraryConstantSignature class.
                    //
                    //The function used in this if branch will write appropriate warnings to the console, that
                    //indicate that this module constant is going to be left undefined.
                    continue;
                }

                var sigExists = _libraryDataProvider.GetLibraryConstantSignature(def.Name);

                if (sigExists != null)
                {
                    //This is possible, because the script base class may have a constant with the same name as 
                    //one in registered in a loaded module.  This however is an error on the module
                    //writers part and should not be allowed.

                    //The IScriptModuleComms object will not allow you to register duplicate constants among
                    //modules.  Therefore if there is a duplicate, it means that a module writer duplicated
                    //the name of a script constant that exists in the script base class.

                    throw new Exception(
                        string.Format(
                            LogHeader + " Module constant '{0}' has a duplicate definition in ScriptBaseClass. "
                            + "Offending Module/Type where it was redefined is un-reportable!",
                            sigExists));
                }

                def.Subsets.Add("os-ModuleConstants");

                //This is a registered module script constant, LibLSLCC is going to need to expand
                //its defined value into the generated source code like a pre-processor would
                def.Expand = true;

                _libraryDataProvider.DefineConstant(def);
            }



            //The following is a hack, because OpenSim does not keep information about event signatures around, just the names.
            var eventData = GetEmbeddedLibraryEventData();

            //Define them, the subset name for events in the embedded resource is os-Events,
            //which matches the subset we have defined above.
            _libraryDataProvider.DefineEventHandlers(eventData.LibraryEvents);
        }




        public void ReadConfig()
        {
            // Get some config
            var configSource = m_scriptEngine.Config.ConfigSource;

            IConfig libLslccConfig;
            if ((libLslccConfig = configSource.Configs["LibLSLCC"]) != null)
            {
                EnableCompilerWarnings = libLslccConfig.GetBoolean("EnableCompilerWarnings", true);
                CreateClassWrapperForCSharpScripts = libLslccConfig.GetBoolean("CreateClassWrapperForCSharpScripts",
                    true);
                CreateClassWrapperForVBScripts = libLslccConfig.GetBoolean("CreateClassWrapperForVBScripts", true);
            }
            else
            {
                CreateClassWrapperForVBScripts = true;
                CreateClassWrapperForCSharpScripts = true;
                EnableCompilerWarnings = true;
            }


            WriteScriptSourceToDebugFile = m_scriptEngine.Config.GetBoolean("WriteScriptSourceToDebugFile", false);
            CompileWithDebugInformation = m_scriptEngine.Config.GetBoolean("CompileWithDebugInformation", true);
            bool deleteScriptsOnStartup = m_scriptEngine.Config.GetBoolean("DeleteScriptsOnStartup", true);

            //force co-op termination calls to be inserted un-conditionally.
            //it does not hurt for them to be there when co-op stop is not
            //actually enabled in XEngine.  This way there does not need to be any
            //recompile when going from preemptive stop mode to co-op stop mode
            m_insertCoopTerminationCalls = true;
            //m_scriptEngine.Config.GetString("ScriptStopStrategy", "abort") == "co-op";

            // Get file prefix from script-engine name and make it file system safe:
            FilePrefix = "CommonCompiler";
            foreach (char c in Path.GetInvalidFileNameChars())
            {
                FilePrefix = FilePrefix.Replace(c, '_');
            }

            if (in_startup)
            {
                in_startup = false;
                CheckOrCreateScriptsDirectory();

                // First time we start? Delete old files
                if (deleteScriptsOnStartup)
                    DeleteOldFiles();
            }

            // Map name and enum type of our supported languages
            LanguageMapping.Add(CompileLanguage.csraw.ToString(), CompileLanguage.csraw);
            LanguageMapping.Add(CompileLanguage.cs.ToString(), CompileLanguage.cs);
            LanguageMapping.Add(CompileLanguage.vb.ToString(), CompileLanguage.vb);
            LanguageMapping.Add(CompileLanguage.vbraw.ToString(), CompileLanguage.vbraw);
            LanguageMapping.Add(CompileLanguage.lsl.ToString(), CompileLanguage.lsl);


            // Allowed compilers
            string allowComp = m_scriptEngine.Config.GetString("AllowedCompilers", "lsl");
            AllowedCompilers.Clear();


#if DEBUG
            m_log.Debug("[Compiler]: Allowed languages: " + allowComp);
#endif


            foreach (string strl in allowComp.Split(','))
            {
                string strlan = strl.Trim(" \t".ToCharArray()).ToLower();
                if (!LanguageMapping.ContainsKey(strlan))
                {
                    m_log.Error("[Compiler]: Config error. Compiler is unable to recognize language type \"" + strlan +
                                "\" specified in \"AllowedCompilers\".");
                }
                else
                {
#if DEBUG
                    //m_log.Debug("[Compiler]: Config OK. Compiler recognized language type \"" + strlan + "\" specified in \"AllowedCompilers\".");
#endif
                }
                AllowedCompilers.Add(strlan, true);
            }


            if (AllowedCompilers.Count == 0)
            {
                m_log.Error(
                    "[Compiler]: Config error. Compiler could not recognize any language in \"AllowedCompilers\". Scripts will not be executed!");
            }

            // Default language
            string defaultCompileLanguage = m_scriptEngine.Config.GetString("DefaultCompileLanguage", "lsl").ToLower();

            // Is this language recognized at all?
            if (!LanguageMapping.ContainsKey(defaultCompileLanguage))
            {
                m_log.Error("[Compiler]: " +
                            "Config error. Default language \"" + defaultCompileLanguage +
                            "\" specified in \"DefaultCompileLanguage\" is not recognized as a valid language. Changing default to: \"lsl\".");
                defaultCompileLanguage = "lsl";
            }

            // Is this language in allow-list?
            if (!AllowedCompilers.ContainsKey(defaultCompileLanguage))
            {
                m_log.Error("[Compiler]: " +
                            "Config error. Default language \"" + defaultCompileLanguage +
                            "\"specified in \"DefaultCompileLanguage\" is not in list of \"AllowedCompilers\". Scripts may not be executed!");
            }
            else
            {
#if DEBUG
                //                m_log.Debug("[Compiler]: " +
                //                                            "Config OK. Default language \"" + defaultCompileLanguage + "\" specified in \"DefaultCompileLanguage\" is recognized as a valid language.");
#endif
                // LANGUAGE IS IN ALLOW-LIST
                DefaultCompileLanguage = LanguageMapping[defaultCompileLanguage];
            }

            // We now have an allow-list, a mapping list, and a default language
        }


        /// <summary>
        /// Create the directory where compiled scripts are stored if it does not already exist.
        /// </summary>
        private void CheckOrCreateScriptsDirectory()
        {
            if (!Directory.Exists(ScriptEnginesPath))
            {
                try
                {
                    Directory.CreateDirectory(ScriptEnginesPath);
                }
                catch (Exception ex)
                {
                    m_log.Error("[Compiler]: Exception trying to create ScriptEngine directory \"" + ScriptEnginesPath +
                                "\": " + ex);
                }
            }

            if (!Directory.Exists(Path.Combine(ScriptEnginesPath,
                m_scriptEngine.World.RegionInfo.RegionID.ToString())))
            {
                try
                {
                    Directory.CreateDirectory(Path.Combine(ScriptEnginesPath,
                        m_scriptEngine.World.RegionInfo.RegionID.ToString()));
                }
                catch (Exception ex)
                {
                    m_log.Error("[Compiler]: Exception trying to create ScriptEngine directory \"" +
                                Path.Combine(ScriptEnginesPath,
                                    m_scriptEngine.World.RegionInfo.RegionID.ToString()) + "\": " + ex);
                }
            }
        }


        /// <summary>
        /// Delete old script files
        /// </summary>
        private void DeleteOldFiles()
        {
            foreach (string file in Directory.GetFiles(Path.Combine(ScriptEnginesPath,
                m_scriptEngine.World.RegionInfo.RegionID.ToString()), FilePrefix + "_compiled*"))
            {
                try
                {
                    File.Delete(file);
                }
                catch (Exception ex)
                {
                    m_log.Error("[Compiler]: Exception trying delete old script file \"" + file + "\": " + ex);
                }
            }
            foreach (string file in Directory.GetFiles(Path.Combine(ScriptEnginesPath,
                m_scriptEngine.World.RegionInfo.RegionID.ToString()), FilePrefix + "_source*"))
            {
                try
                {
                    File.Delete(file);
                }
                catch (Exception ex)
                {
                    m_log.Error("[Compiler]: Exception trying delete old script file \"" + file + "\": " + ex);
                }
            }
        }


        public string GetCompilerOutput(string assetID)
        {
            return Path.Combine(ScriptEnginesPath, Path.Combine(
                m_scriptEngine.World.RegionInfo.RegionID.ToString(),
                FilePrefix + "_compiled_" + assetID + ".dll"));
        }


        public void PerformScriptCompile(
            string source, string asset, UUID ownerUUID,
            out string assembly, out Dictionary<KeyValuePair<int, int>, KeyValuePair<int, int>> linemap)
        {
            PerformScriptCompile(source, asset, ownerUUID, false, out assembly, out linemap);
        }


        public void PerformScriptCompile(
            string source, string asset, UUID ownerUUID, bool alwaysRecompile,
            out string assembly, out Dictionary<KeyValuePair<int, int>, KeyValuePair<int, int>> linemap)
        {
            //            m_log.DebugFormat("[Compiler]: Checking script for asset {0} in {1}\n{2}", asset, m_scriptEngine.World.Name, source);


            linemap = null;
            m_warnings.Clear();

            assembly = GetCompilerOutput(asset);

            //            m_log.DebugFormat("[Compiler]: Retrieved assembly {0} for asset {1} in {2}", assembly, asset, m_scriptEngine.World.Name);

            CheckOrCreateScriptsDirectory();

            // Don't recompile if we're not forced to and we already have it
            // Performing 2 file exists tests for every script can still be slow

            //LibLSLCC does not need error map files, all its syntax checking is done on the front end.
            if (!alwaysRecompile && File.Exists(assembly) && File.Exists(assembly + ".text"))
            {
                //m_log.DebugFormat("[Compiler]: Found existing assembly {0} for asset {1} in {2}", assembly, asset, m_scriptEngine.World.Name);

                //no more line map junk!
                return;
            }

            //            m_log.DebugFormat("[Compiler]: Compiling assembly {0} for asset {1} in {2}", assembly, asset, m_scriptEngine.World.Name);

            if (source == string.Empty)
            {
                throw new Exception("Cannot find script assembly and no script text present");
            }


            CompileLanguage language = DefaultCompileLanguage;

            if (source.StartsWith("//c#", true, CultureInfo.InvariantCulture))
            {
                language = CompileLanguage.cs;
            }
            if (source.StartsWith("//c#-raw", true, CultureInfo.InvariantCulture))
            {
                language = CompileLanguage.csraw;
            }
            if (source.StartsWith("//vb-raw", true, CultureInfo.InvariantCulture))
            {
                language = CompileLanguage.vbraw;

                // We need to remove //vb-raw, it won't compile with that
                source = source.Substring(8, source.Length - 8);
            }
            if (source.StartsWith("//vb", true, CultureInfo.InvariantCulture))
            {
                language = CompileLanguage.vb;

                // We need to remove //vb, it won't compile with that
                source = source.Substring(4, source.Length - 4);
            }
            if (source.StartsWith("//lsl", true, CultureInfo.InvariantCulture))
            {
                language = CompileLanguage.lsl;
            }


            //            m_log.DebugFormat("[Compiler]: Compile language is {0}", language);

            if (!AllowedCompilers.ContainsKey(language.ToString()))
            {
                // Not allowed to compile to this language!
                string errtext = string.Empty;
                errtext += "The compiler for language \"" + language +
                           "\" is not in list of allowed compilers. Script will not be executed!";
                throw new Exception(errtext);
            }

            if (m_scriptEngine.World.Permissions.CanCompileScript(ownerUUID, (int) language) == false)
            {
                // Not allowed to compile to this language!
                string errtext = string.Empty;
                errtext += ownerUUID +
                           " is not in list of allowed users for this scripting language. Script will not be executed!";
                throw new Exception(errtext);
            }

            string compileScript = source;

            if (language == CompileLanguage.lsl)
            {
                // Its LSL, convert it to C#
                var converter = new LibLSLCCCodeGenerator(_libraryDataProvider, CreateLslCompilerSettings());


                converter.EmitCompilerWarnings = EnableCompilerWarnings;


                LSL_Converter = converter;
                compileScript = LSL_Converter.Convert(source);

                // copy converter warnings into our warnings.
                foreach (string warning in LSL_Converter.GetWarnings())
                {
                    AddWarning(warning);
                }

                //no more line map junk!
            }

            //the LibLSLCC code generator generates everything, the class, constructor, namespace and imports
            //using the settings we created and gave to it.
            //
            //so we now only need to modify incoming CSharp or VB scripts before compiling them.
            if (language == CompileLanguage.cs && CreateClassWrapperForCSharpScripts)
            {
                compileScript = CreateCSCompilerScript(
                    compileScript,
                    m_scriptEngine.ScriptClassName,
                    m_scriptEngine.ScriptBaseClassName,
                    m_scriptEngine.ScriptBaseClassParameters);
            }

            if (language == CompileLanguage.vb && CreateClassWrapperForVBScripts)
            {
                compileScript = CreateVBCompilerScript(
                    compileScript,
                    m_scriptEngine.ScriptClassName,
                    m_scriptEngine.ScriptBaseClassName);
            }

            assembly = CompileFromDotNetText(compileScript, language, asset, assembly);
        }


        public string[] GetWarnings()
        {
            return m_warnings.ToArray();
        }


        private void AddWarning(string warning)
        {
            if (!m_warnings.Contains(warning))
            {
                m_warnings.Add(warning);
            }
        }


        private LSLOpenSimCompilerSettings CreateLslCompilerSettings()
        {
            var constructorParameters = m_scriptEngine.ScriptBaseClassParameters;

            var constructorSigParams = constructorParameters != null
                ? string.Join(", ", Array.ConvertAll(constructorParameters, pi => pi.ToString()))
                : "";

            var constructorSigParamNames = constructorParameters != null
                ? string.Join(", ", Array.ConvertAll(constructorParameters, pi => pi.Name))
                : "";

            var constructorSig = "(" + constructorSigParams + ") : base(" + constructorSigParamNames + ")";


            var compilerSettings = new LSLOpenSimCompilerSettings
            {
                GenerateClass = true,
                GeneratedClassNamespace = "SecondLife",
                GeneratedClassName = m_scriptEngine.ScriptClassName,
                GeneratedInheritanceList = m_scriptEngine.ScriptBaseClassName,
                GeneratedConstructorSignature = constructorSig,
                InsertCoOpTerminationCalls = m_insertCoopTerminationCalls,
                CoOpTerminationFunctionCall = "opensim_reserved_CheckForCoopTermination()",
                GeneratedClassAccessibility = ClassAccessibilityLevel.Default,
                GeneratedConstructorAccessibility = MemberAccessibilityLevel.Public
            };

            compilerSettings.GeneratedNamespaceImports.Add("System.Collections.Generic");
            compilerSettings.GeneratedNamespaceImports.Add("OpenSim.Region.ScriptEngine.Shared");


            return compilerSettings;
        }


        private static string CreateCSCompilerScript(
            string compileScript, string className, string baseClassName, ParameterInfo[] constructorParameters)
        {
            compileScript = string.Format(
                @"using OpenSim.Region.ScriptEngine.Shared; 
using System.Collections.Generic;

namespace SecondLife 
{{ 
    public class {0} : {1} 
    {{
        public {0}({2}) : base({3}) {{}}
{4}
    }}
}}",
                className,
                baseClassName,
                constructorParameters != null
                    ? string.Join(", ",
                        Array.ConvertAll(constructorParameters, pi => pi.ToString()))
                    : "",
                constructorParameters != null
                    ? string.Join(", ", Array.ConvertAll(constructorParameters, pi => pi.Name))
                    : "",
                compileScript);

            return compileScript;
        }


        private static string CreateVBCompilerScript(string compileScript, string className, string baseClassName)
        {
            compileScript = string.Empty +
                            "Imports OpenSim.Region.ScriptEngine.Shared: Imports System.Collections.Generic: " +
                            string.Empty + "NameSpace SecondLife:" +
                            string.Empty + "Public Class " + className + ": Inherits " + baseClassName +
                            "\r\nPublic Sub New()\r\nEnd Sub: " +
                            compileScript +
                            ":End Class :End Namespace\r\n";

            return compileScript;
        }

        /// <summary>
        /// Compile .NET script to .Net assembly (.dll)
        /// </summary>
        /// <param name="script">CS script</param>
        /// <returns>Filename to .dll assembly</returns>
        internal string CompileFromDotNetText(string script, CompileLanguage lang, string asset, string assembly)
        {
            //            m_log.DebugFormat("[Compiler]: Compiling to assembly\n{0}", Script);

            string ext = "." + lang;

            // Output assembly name
            try
            {
                if (File.Exists(assembly))
                {
                    File.SetAttributes(assembly, FileAttributes.Normal);
                    File.Delete(assembly);
                }
            }
            catch (Exception e) // NOTLEGIT - Should be just FileIOException
            {
                throw new Exception("Unable to delete old existing " +
                                    "script-file before writing new. Compile aborted: " +
                                    e);
            }

            // DEBUG - write source to disk
            if (WriteScriptSourceToDebugFile)
            {
                string srcFileName = FilePrefix + "_source_" +
                                     Path.GetFileNameWithoutExtension(assembly) + ext;
                try
                {
                    File.WriteAllText(Path.Combine(Path.Combine(
                        ScriptEnginesPath,
                        m_scriptEngine.World.RegionInfo.RegionID.ToString()),
                        srcFileName), script);
                }
                catch (Exception ex) //NOTLEGIT - Should be just FileIOException
                {
                    m_log.Error("[Compiler]: Exception while " +
                                "trying to write script source to file \"" +
                                srcFileName + "\": " + ex);
                }
            }

            // Do actual compile
            CompilerParameters parameters = new CompilerParameters();

            parameters.IncludeDebugInformation = true;

            string rootPath = AppDomain.CurrentDomain.BaseDirectory;

            parameters.ReferencedAssemblies.Add(Path.Combine(rootPath,
                "OpenSim.Region.ScriptEngine.Shared.dll"));
            parameters.ReferencedAssemblies.Add(Path.Combine(rootPath,
                "OpenSim.Region.ScriptEngine.Shared.Api.Runtime.dll"));
            parameters.ReferencedAssemblies.Add(Path.Combine(rootPath,
                "OpenMetaverseTypes.dll"));

            if (m_scriptEngine.ScriptReferencedAssemblies != null)
                Array.ForEach(
                    m_scriptEngine.ScriptReferencedAssemblies,
                    a => parameters.ReferencedAssemblies.Add(Path.Combine(rootPath, a)));

            parameters.GenerateExecutable = false;
            parameters.OutputAssembly = assembly;
            parameters.IncludeDebugInformation = CompileWithDebugInformation;
            //parameters.WarningLevel = 1; // Should be 4?
            parameters.TreatWarningsAsErrors = false;

            CompilerResults results;
            switch (lang)
            {
                case CompileLanguage.vbraw:
                case CompileLanguage.vb:
                    results = VBcodeProvider.CompileAssemblyFromSource(
                        parameters, script);
                    break;
                case CompileLanguage.csraw:
                case CompileLanguage.cs:
                case CompileLanguage.lsl:
                    bool complete = false;
                    bool retried = false;
                    do
                    {
                        lock (CScodeProvider)
                        {
                            results = CScodeProvider.CompileAssemblyFromSource(
                                parameters, script);
                        }

                        // Deal with an occasional segv in the compiler.
                        // Rarely, if ever, occurs twice in succession.
                        // Line # == 0 and no file name are indications that
                        // this is a native stack trace rather than a normal
                        // error log.
                        if (results.Errors.Count > 0)
                        {
                            if (!retried && string.IsNullOrEmpty(results.Errors[0].FileName) &&
                                results.Errors[0].Line == 0)
                            {
                                // System.Console.WriteLine("retrying failed compilation");
                                retried = true;
                            }
                            else
                            {
                                complete = true;
                            }
                        }
                        else
                        {
                            complete = true;
                        }
                    } while (!complete);
                    break;
                default:
                    throw new Exception("Compiler is not able to recognize " +
                                        "language type \"" + lang + "\"");
            }

            //
            // WARNINGS AND ERRORS
            //
            bool hadErrors = false;
            string errtext = string.Empty;
            if (results.Errors.Count > 0)
            {
                foreach (CompilerError CompErr in results.Errors)
                {
                    string severity = CompErr.IsWarning ? "Warning" : "Error";


                    // Show 5 errors max, but check entire list for errors

                    if (severity == "Error")
                    {
                        string text = CompErr.ErrorText;

                        // The Second Life viewer's script editor begins
                        // counting lines and columns at 0, so we subtract 1.
                        errtext += string.Format("({0},{1}): {4} {2}: {3}\n",
                            CompErr.Line - 1, CompErr.Column - 1,
                            CompErr.ErrorNumber, text, severity);
                        hadErrors = true;
                    }
                }
            }

            if (hadErrors)
            {
                throw new Exception(errtext);
            }

            //  On today's highly asynchronous systems, the result of
            //  the compile may not be immediately apparent. Wait a 
            //  reasonable amount of time before giving up on it.

            if (!File.Exists(assembly))
            {
                for (int i = 0; i < 20 && !File.Exists(assembly); i++)
                {
                    Thread.Sleep(250);
                }
                // One final chance...
                if (!File.Exists(assembly))
                {
                    errtext = string.Empty;
                    errtext += "No compile error. But not able to locate compiled file.";
                    throw new Exception(errtext);
                }
            }

            //            m_log.DebugFormat("[Compiler] Compiled new assembly "+
            //                    "for {0}", asset);

            // Because windows likes to perform exclusive locks, we simply
            // write out a textual representation of the file here
            //
            // Read the binary file into a buffer
            //
            FileInfo fi = new FileInfo(assembly);

            //could not stat
            if (fi == null)
            {
                errtext = string.Empty;
                errtext += "No compile error. But not able to stat file.";
                throw new Exception(errtext);
            }

            byte[] data = new byte[fi.Length];

            try
            {
                using (FileStream fs = File.Open(assembly, FileMode.Open, FileAccess.Read))
                {
                    fs.Read(data, 0, data.Length);
                }
            }
            catch (Exception)
            {
                errtext = string.Empty;
                errtext += "No compile error. But not able to open file.";
                throw new Exception(errtext);
            }

            // Convert to base64
            //
            string filetext = Convert.ToBase64String(data);

            byte[] buf = Encoding.ASCII.GetBytes(filetext);

            using (FileStream sfs = File.Create(assembly + ".text"))
                sfs.Write(buf, 0, buf.Length);

            return assembly;
        }
    }
}