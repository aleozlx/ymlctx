extern crate yaml_rust;
extern crate rpds;

#[macro_use]
extern crate serde_derive;

#[cfg(feature = "topyobject")]
extern crate pyo3;

#[cfg(feature = "topyobject")]
mod context_py {
    use pyo3::prelude::*;
    use pyo3::Python;
    use pyo3::types::PyDict;
//     use pyo3::ObjectProtocol;
//     use pyo3::class::basic::{PyObjectProtocol};

//     // class Context(dict):
//     //     def __getattr__(self, name):
//     //         return self[name]

//     #[pyclass(dict)]
//     struct Context {}

//     #[pyproto]
//     impl PyObjectProtocol for Context {
//         fn __getattr__(&self, name: &PyString) -> PyResult<()> {
//             let a = self.get_base().get_item(name);
//             Ok(())
//         }
//     }

    /// Wrap a Python dict into a type equivalent to this:
    /// 
    /// ```python
    /// class Context(dict):
    ///     def __getattr__(self, name):
    ///         return self[name]
    /// ```
    /// 
    /// This type is used to pass contexts around in Python, which makes it easier to refer to their elements
    /// using the attribute syntax instead of an indexer + string, e.g.
    /// 
    /// ```python
    /// # no more ctx['var'], just
    /// ctx.var
    /// ```
    pub fn wrapper(obj: PyObject, py: Python) -> PyObject {
        let locals = PyDict::new(py);
        locals.set_item("obj", obj).unwrap();
        py.eval("type('Context', (dict,), { '__getattr__': lambda self, name: self[name] })(obj)", None, Some(&locals)).unwrap().to_object(py)
    }
}

pub mod context {
    use yaml_rust::{Yaml, YamlLoader, YamlEmitter};
    use std::ops::Index;
    use rpds::HashTrieMap;
    use std::fmt::{Display, Formatter};

    #[cfg(feature = "topyobject")]
    use pyo3::prelude::*;
    #[cfg(feature = "topyobject")]
    use pyo3::Python;
    #[cfg(feature = "topyobject")]
    use pyo3::types::{PyDict, PyString, PyList};

    /// A data structure designed to provide a high-level language agnostic calling convention.
    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub struct Context {
        data: HashTrieMap<String, CtxObj>
    }

    /// Enum of all primitive types that a Ccntext is composed of.
    #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
    pub enum CtxObj {
        Str(String),
        Bin(Vec<u8>),
        Int(i64),
        Real(f64),
        Bool(bool),
        Array(Vec<CtxObj>),
        Context(Context),
        None
    }

    /// The error type for the low-level unpack() functions.
    /// This error occurs when either the key does not exist or it is not feasible to convert into the deduced type.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct CtxObjUnpackError {}

    /// Unpack data from some context element into a Rust primitive/standard type.
    /// The destination type can usually be deduced to save type annotations as well.
    pub trait CtxObjUnpack: Sized {
        fn unpack(src: CtxObj) -> Option<Self>;
    }

    impl CtxObjUnpack for String {
        fn unpack(src: CtxObj) -> Option<Self> {
            if let CtxObj::Str(val) = src {
                Some(val)
            }
            else { None }
        }
    }

    impl CtxObjUnpack for i64 {
        fn unpack(src: CtxObj) -> Option<Self> {
            if let CtxObj::Int(val) = src {
                Some(val)
            }
            else { None }
        }
    }

    impl CtxObjUnpack for i32 {
        fn unpack(src: CtxObj) -> Option<Self> {
            if let CtxObj::Int(val) = src {
                Some(val as Self)
            }
            else { None }
        }
    }

    impl CtxObjUnpack for usize {
        fn unpack(src: CtxObj) -> Option<Self> {
            if let CtxObj::Int(val) = src {
                Some(val as Self)
            }
            else { None }
        }
    }

    impl CtxObjUnpack for f64 {
        fn unpack(src: CtxObj) -> Option<Self> {
            if let CtxObj::Real(val) = src {
                Some(val)
            }
            else { None }
        }
    }

    impl CtxObjUnpack for bool {
        fn unpack(src: CtxObj) -> Option<Self> {
            if let CtxObj::Bool(val) = src {
                Some(val)
            }
            else { None }
        }
    }

    impl From<Yaml> for CtxObj {
        fn from(src: Yaml) -> CtxObj {
            match src {
                Yaml::String(val) => { CtxObj::Str(val.to_owned()) },
                Yaml::Boolean(val) => { CtxObj::Bool(val.to_owned()) },
                Yaml::Integer(val) => { CtxObj::Int(val.to_owned()) },
                Yaml::Real(val) => { CtxObj::Real(val.parse().unwrap()) }
                Yaml::Null => { CtxObj::None },
                Yaml::Hash(_) => { CtxObj::Context(Context::from(src)) },
                Yaml::Array(val) => {
                    CtxObj::Array(val.iter().map(|i| { CtxObj::from(i.clone()) }).collect()) 
                },
                Yaml::Alias(_val) => {
                    unimplemented!();
                },
                Yaml::BadValue => { unreachable!(); },
            }
        }
    }

    impl Into<Yaml> for CtxObj {
        fn into(self) -> Yaml {
            match self {
                CtxObj::Str(val) => Yaml::String(val.to_owned()),
                CtxObj::Bool(val) => Yaml::Boolean(val.to_owned()),
                CtxObj::Int(val) => Yaml::Integer(val.to_owned()),
                CtxObj::Real(val) => Yaml::Real(val.to_string()),
                CtxObj::None => Yaml::Null,
                CtxObj::Context(val) => val.clone().into(),
                CtxObj::Array(val) => Yaml::Array(val.iter().map(|i| {i.clone().into()}).collect()),
                CtxObj::Bin(_) => unimplemented!()
            }
        }
    }

    #[cfg(feature = "topyobject")]
    impl ToPyObject for CtxObj {
        fn to_object(&self, py: Python) -> PyObject {
            match self {
                CtxObj::None => py.None(),
                CtxObj::Str(val) => val.to_object(py),
                CtxObj::Bool(val) => val.to_object(py),
                CtxObj::Int(val) => val.to_object(py),
                CtxObj::Real(val) => val.to_object(py),
                CtxObj::Context(val) => val.to_object(py),
                CtxObj::Array(val) => {
                    let tmp: Vec<PyObject> = val.iter().map(|i| {i.to_object(py)}).collect();
                    PyList::new(py, &tmp).to_object(py)
                },
                CtxObj::Bin(val) => val.to_object(py)
            }
        }
    }

    impl From<Yaml> for Context {
        fn from(src: Yaml) -> Self {
            let mut context_data = HashTrieMap::new();
            if let Yaml::Hash(raw) = src {
                for (k, v) in raw {
                    if let Yaml::String(key) = k {
                        match v {
                            Yaml::String(_) | Yaml::Boolean(_) | Yaml::Integer(_) | Yaml::Real(_) | Yaml::Null | Yaml::Hash(_) | Yaml::Array(_) | Yaml::Alias(_) => {
                                context_data.insert_mut(key.to_owned(), CtxObj::from(v));
                            }
                            Yaml::BadValue => { }
                        }
                    }
                }
            }
            Context { data: context_data }
        }
    }

    impl<'a> From<&'a str> for Context {
        fn from(s: &str) -> Self {
            Context::from(YamlLoader::load_from_str(s).unwrap()[0].clone())
        }
    }

    impl Into<Yaml> for Context {
        fn into(self) -> Yaml {
            let mut map = yaml_rust::yaml::Hash::new();
            for (k, v) in self.data.iter() {
                map.insert(Yaml::String(k.to_owned()), v.to_owned().into());
            }
            Yaml::Hash(map)
        }
    }

    #[cfg(feature = "topyobject")]
    impl ToPyObject for Context {
        fn to_object(&self, py: Python) -> PyObject {
            let ctx = PyDict::new(py);
            for (k, v) in self.data.iter() {
                ctx.set_item(PyString::new(py, k), v.to_object(py)).unwrap();
            }
            crate::context_py::wrapper(ctx.to_object(py), py)
        }
    }

    impl Display for Context {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let mut out_str = String::new();
            {
                let mut emitter = YamlEmitter::new(&mut out_str);
                emitter.dump(&self.clone().into()).unwrap();
            }
            write!(f, "{}", &out_str)
        }
    }

    impl<'a> Index<&'a str> for Context {
        type Output = CtxObj;

        fn index(&self, key: &'a str) -> &CtxObj {
            self.data.get(key).expect(&format!("Key error: {}", key))
        }
    }

    impl Context {
        /// Create an empty context.
        pub fn new() -> Context {
            Context { data: HashTrieMap::new() }
        }

        /// Overlay `another` on top of this context.
        /// 
        /// **Example**
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::Context;
        /// let eg = Context::from("a: 1\nb: 0");
        /// let another = Context::from("b: 1");
        /// assert_eq!(eg.overlay(&another), Context::from("a: 1\nb: 1"));
        /// ```
        pub fn overlay(&self, another: &Context) -> Context {
            let mut forward_snapshot = self.data.clone();
            for (k, v) in another.data.iter() {
                forward_snapshot.insert_mut(k.to_owned(), v.to_owned());
            }
            Context { data: forward_snapshot }
        }

        /// Set a context element.
        ///
        /// **Example**
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj};
        /// let eg = Context::from("a: 1\nb: 0");
        /// assert_eq!(eg.set("b", CtxObj::Int(1)), Context::from("a: 1\nb: 1"));
        /// ```
        pub fn set(&self, key: &str, val: CtxObj) -> Context {
            Context { data: self.data.insert(key.to_owned(), val) }
        }

        /// Optionally set a context element. (Syntax sugar to adapt to Option<CtxObj>)
        ///
        /// **Example**
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj};
        /// let eg = Context::from("a: 1\nb: 0");
        /// assert_eq!(eg.set_opt("b", Some(CtxObj::Int(1))), Context::from("a: 1\nb: 1"));
        /// assert_eq!(eg.set_opt("b", None), Context::from("a: 1\nb: 0"));
        /// ```
        pub fn set_opt(&self, key: &str, optional: Option<CtxObj>) -> Context {
            match optional {
                Some(val) => Context { data: self.data.insert(key.to_owned(), val) },
                None => self.clone()
            }
        }

        /// Get an element *by reference* if the key exists.
        ///
        /// **Example**
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("a: 1");
        /// assert_eq!(eg.get("a").unwrap().clone(), CtxObj::Int(1));
        /// assert_eq!(eg.get("b"), None);
        /// ```
        pub fn get(&self, key: &str) -> Option<&CtxObj> {
            self.data.get(key)
        }

        /// Get an element *by value* if the key exists.
        ///
        /// **Example**
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("a: 1");
        /// assert_eq!(eg.get_clone("a").unwrap(), CtxObj::Int(1));
        /// assert_eq!(eg.get_clone("b"), None);
        /// ```
        pub fn get_clone(&self, key: &str) -> Option<CtxObj> {
            match self.data.get(key) {
                Some(p) => Some(p.clone()),
                None => None
            }
        }

        /// Unpack an element by key if it exists.
        ///
        /// **Example**
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("a: 1");
        /// let success: i64 = eg.unpack("a").unwrap();
        /// assert_eq!(success, 1);
        /// 
        /// /*Although, beware of auto-conversion due to polymorphism with the CtxObjUnpack trait.*/
        /// let success: i32 = eg.unpack("a").unwrap();
        /// assert_eq!(success, 1);
        /// ```
        /// This should fail because the key specified does not exist.
        /// ```rust,should_panic
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("a: 1");
        /// let err: i64 = match eg.unpack("b") {
        ///     Ok(v) => v,
        ///     Err(_) => panic!()
        /// };
        /// ```
        /// 
        /// This should also fail because the type conversion is not feasible.
        /// ```rust,should_panic
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("a: 1");
        /// let err: String = match eg.unpack("b") {
        ///     Ok(v) => v,
        ///     Err(_) => panic!()
        /// };
        /// ```
        pub fn unpack<T: CtxObjUnpack>(&self, key: &str) -> Result<T, CtxObjUnpackError> {
            if let Some(o) = self.data.get(key) {
                if let Some(v) = T::unpack(o.to_owned()) { Ok(v) }
                else { Err(CtxObjUnpackError{ }) }
            }
            else { Err(CtxObjUnpackError{ }) }
        }

        /// Enter a nested context.
        /// 
        /// **Example**
        /// 
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("s:\n  a: 1");
        /// assert_eq!(eg.subcontext("s"), Some(Context::from("a: 1")));
        /// ```
        pub fn subcontext(&self, key: &str) -> Option<Context> {
            if let Some(CtxObj::Context(val)) = self.data.get(key) { Some(val.clone()) }
            else { None }
        }

        /// List nested contexts.
        /// 
        /// **Example**
        /// 
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("s:\n- a: 1\n- b: 1");
        /// assert_eq!(eg.list_contexts("s"), Some(vec![Context::from("a: 1"), Context::from("b: 1")]));
        /// ```
        pub fn list_contexts(&self, key: &str) -> Option<Vec<Context>> {
            if let Some(CtxObj::Array(val)) = self.data.get(key) {
                let mut ret = Vec::new();
                for i in val.iter() {
                    if let CtxObj::Context(ctx) = i {
                        ret.push(ctx.clone());
                    }
                }
                return Some(ret);
            }
            else { None }
        }

        /// Hide an element by key if it exists.
        /// 
        /// **Example**
        /// 
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("a: 1\nb: 1");
        /// assert_eq!(eg.hide("b"), Context::from("a: 1"));
        /// assert_eq!(eg.hide("c"), eg);
        /// ```
        pub fn hide(&self, key: &str) -> Context {
            Context { data: self.data.remove(key) }
        }

        /// Get all keys from this context.
        /// 
        /// **Example**
        /// 
        /// ```
        /// # extern crate ymlctx;
        /// # use ymlctx::context::{Context, CtxObj, CtxObjUnpack};
        /// let eg = Context::from("a: 1\nb: 1");
        /// let keys: std::collections::HashSet<String> = eg.keys().map(|k| { k.to_owned() }).collect();
        /// assert_eq!(keys, vec![String::from("a"), String::from("b")].into_iter().collect());
        /// ```
        pub fn keys(&self) -> rpds::map::hash_trie_map::IterKeys<String, CtxObj> {
            self.data.keys()
        }
    }
}

#[cfg(test)]
mod tests{
    use crate::context::Context;

    #[test]
    fn multiple_overwrites() {
        let a = Context::from("a: 1\nb: 0");
        let b = Context::from("a: 0\nb: 1");
        let c = a.overlay(&b);
        assert_eq!(c, b);
    }

    #[test]
    fn single_overwrite() {
        let a = Context::from("a: 1\nb: 0");
        let b = Context::from("b: 1");
        let c = a.overlay(&b);
        assert_eq!(c, Context::from("a: 1\nb: 1"));
    }

    #[test]
    fn insertion() {
        let a = Context::from("a: 1\nb: 0");
        let b = Context::from("c: 1");
        let c = a.overlay(&b);
        assert_eq!(c, Context::from("a: 1\nb: 0\nc: 1"));
    }

    #[test]
    fn subcontext() {
        let a = Context::from("a: 1\nb:\n  b1: 1\n  b2: 1");
        let b = Context::from("b1: 1\nb2: 1");
        assert_eq!(a.subcontext("b").unwrap(), b);
    }

    #[test]
    fn list_contexts() {
        let a = Context::from("a: 1\nb:\n- b1: 1\n- b2: 1");
        assert_eq!(a.list_contexts("b").unwrap(), vec![Context::from("b1: 1"), Context::from("b2: 1")]);
    }

    #[test]
    fn hide_existing() {
        let a = Context::from("a: 1\nb: 0");
        assert_eq!(a.hide("b"), Context::from("a: 1\n"));
    }

    #[test]
    fn hide_nonexisting() {
        let a = Context::from("a: 1\nb: 0");
        assert_eq!(a.hide("c"), Context::from("a: 1\nb: 0"));
    }

    #[test]
    fn unpack_string() {
        let a = Context::from("a: test");
        let out: String = a.unpack("a").unwrap();
        assert_eq!(out, String::from("test"));
    }

    #[test]
    fn unpack_i64() {
        let a = Context::from("a: 1");
        let out: i64 = a.unpack("a").unwrap();
        assert_eq!(out, 1);
    }

    #[test]
    fn unpack_i32() {
        let a = Context::from("a: 1");
        let out: i32 = a.unpack("a").unwrap();
        assert_eq!(out, 1);
    }

    #[test]
    fn unpack_usize() {
        let a = Context::from("a: 1");
        let out: usize = a.unpack("a").unwrap();
        assert_eq!(out, 1);
    }

    #[test]
    fn unpack_f64() {
        let a = Context::from("a: 1.2");
        let out: f64 = a.unpack("a").unwrap();
        assert_eq!(out, 1.2);
    }

    #[test]
    fn unpack_bool() {
        let a = Context::from("a: true");
        let out: bool = a.unpack("a").unwrap();
        assert_eq!(out, true);
    }


}

#[cfg(test)]
#[cfg(feature = "topyobject")]
mod tests_py {
    use crate::context::Context;
    use pyo3::prelude::*;
    use pyo3::Python;
    use pyo3::types::PyDict;

    fn pystr(obj: &PyObject, py: Python) -> PyResult<String> {
        let locals = PyDict::new(py);
        locals.set_item("obj", obj).unwrap();
        Ok(py.eval("str(obj)", None, Some(locals))?.extract()?)
    }

    fn pystr_attr_a(obj: &PyObject, py: Python) -> PyResult<String> {
        let locals = PyDict::new(py);
        locals.set_item("obj", obj).unwrap();
        Ok(py.eval("str(obj.a)", None, Some(locals))?.extract()?)
    }

    #[test]
    fn ctx2py() {
        let a = Context::from("a: 1");
        let gil = Python::acquire_gil();
        let py = gil.python();
        let ret: PyObject = a.to_object(py);

        if let Ok(ret_str) = pystr(&ret, py) {
            assert_eq!(ret_str, String::from("{'a': 1}"));
        }
        else {
            assert!(false);
        }
    }

    #[test]
    fn ctx2py_attr_a() {
        let a = Context::from("a: 1");
        let gil = Python::acquire_gil();
        let py = gil.python();
        let ret: PyObject = a.to_object(py);

        if let Ok(ret_str) = pystr_attr_a(&ret, py) {
            assert_eq!(ret_str, String::from("1"));
        }
        else {
            assert!(false);
        }
    }
}
