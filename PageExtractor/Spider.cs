using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Web;
using System.Net;
using System.IO;
using System.Text.RegularExpressions;
using System.Windows;
using System.Windows.Threading;
using System.Threading;
using System.Drawing;
using System.Drawing.Imaging;
using System.Data.SqlClient;

namespace PageExtractor
{
    class Spider
    {
        #region private type
        private class RequestState
        {
            private const int BUFFER_SIZE = 13107200;//接收数据包的空间大小
            private byte[] _data = new byte[BUFFER_SIZE];//接收数据包的buffer
            private StringBuilder _sb = new StringBuilder();//存放所有接收到的字符

            public HttpWebRequest Req { get; private set; }//请求
            public string Url { get; private set; }//请求的URL
            public int Depth { get; private set; }//此次请求的相对深度
            public int Index { get; private set; }//工作实例的编号
            public Stream ResStream { get; set; }//接收数据流
            public StringBuilder Html
            {
                get
                {
                    return _sb;
                }
            }
            
            public byte[] Data
            {
                get
                {
                    return _data;
                }
            }

            public int BufferSize
            {
                get
                {
                    return BUFFER_SIZE;
                }
            }

            public RequestState(HttpWebRequest req, string url, int depth, int index)
            {
                Req = req;
                Url = url;
                Depth = depth;
                Index = index;
            }
        }

        private class WorkingUnitCollection
        {
            private int _count;
            //private AutoResetEvent[] _works;
            private bool[] _busy;

            public WorkingUnitCollection(int count)
            {
                _count = count;
                //_works = new AutoResetEvent[count];
                _busy = new bool[count];

                for (int i = 0; i < count; i++)
                {
                    //_works[i] = new AutoResetEvent(true);
                    _busy[i] = true;
                }
            }

            public void StartWorking(int index)
            {
                if (!_busy[index])
                {
                    _busy[index] = true;
                    //_works[index].Reset();
                }
            }

            public void FinishWorking(int index)
            {
                if (_busy[index])
                {
                    _busy[index] = false;
                    //_works[index].Set();
                }
            }

            public bool IsFinished()
            {
                bool notEnd = false;
                foreach (var b in _busy)
                {
                    notEnd |= b;
                }
                return !notEnd;
            }

            public void WaitAllFinished()
            {
                while (true)
                {
                    if (IsFinished())
                    {
                        break;
                    }
                    Thread.Sleep(1000);
                }
                //WaitHandle.WaitAll(_works);
            }

            public void AbortAllWork()
            {
                for (int i = 0; i < _count; i++)
                {
                    _busy[i] = false;
                }
            }
        }
        #endregion

        #region private fields
        private static Encoding GB18030 = Encoding.GetEncoding("GB18030");   // GB18030兼容GBK和GB2312
        private static Encoding UTF8 = Encoding.UTF8;
        private string _userAgent = "Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 6.1; Trident/4.0)";
        private string _accept = "text/html";
        private string _method = "GET";
        private Encoding _encoding = GB18030;
        private Encodings _enc = Encodings.GB;
        private int _maxTime = 2 * 60 * 1000;//异步请求超时时间

        private int _index;
        private string _path = null;
        private int _maxDepth = 2;
        private string _rootUrl = null;
        private string _baseUrl = null;
        private Dictionary<string, int> _urlsLoaded = new Dictionary<string, int>();
        private Dictionary<string, int> _urlsUnload = new Dictionary<string, int>();

        private bool _stop = true;
        private Timer _checkTimer = null;
        private readonly object _locker = new object();
        private bool[] _reqsBusy = null;//每个元素代表一个工作实例是否正在工作
        private int _reqCount = 4;//工作实例的数量，默认为4个
        private WorkingUnitCollection _workingSignals;
        #endregion

        #region constructors
        /// <summary>
        /// 创建一个Spider实例
        /// </summary>
        public Spider()
        {
        }
        #endregion

        #region properties
        /// <summary>
        /// 下载根Url
        /// </summary>
        public string RootUrl
        {
            get
            {
                return _rootUrl;
            }
            set
            {
                if (!value.Contains("http://"))
                {
                    _rootUrl = "http://" + value;
                }
                else
                {
                    _rootUrl = value;
                }
                _baseUrl = _rootUrl.Replace("www.", "");
                _baseUrl = _baseUrl.Replace("http://", "");
                _baseUrl = _baseUrl.TrimEnd('/');
                //Console.WriteLine(_baseUrl+" "+_rootUrl+"\n");
            }
        }

        /// <summary>
        /// 网页编码类型
        /// </summary>
        public Encodings PageEncoding
        {
            get
            {
                return _enc;
            }
            set
            {
                _enc = value;
                switch (value)
                {
                    case Encodings.GB:
                        _encoding = GB18030;
                        break;
                    case Encodings.UTF8:
                        _encoding = UTF8;
                        break;
                }
            }
        }

        /// <summary>
        /// 最大下载深度
        /// </summary>
        public int MaxDepth
        {
            get
            {
                return _maxDepth;
            }
            set
            {
                _maxDepth = Math.Max(value, 1);
            }
        }

        /// <summary>
        /// 下载最大连接数
        /// </summary>
        public int MaxConnection
        {
            get
            {
                return _reqCount;
            }
            set
            {
                _reqCount = value;
            }
        }
        #endregion

        #region public type
        public delegate void ContentsSavedHandler(string path, string url);

        public delegate void DownloadFinishHandler(int count);

        public enum Encodings
        {
            UTF8,
            GB
        }
        #endregion

        #region events
        /// <summary>
        /// 正文内容被保存到本地后触发
        /// </summary>
        public event ContentsSavedHandler ContentsSaved = null;

        /// <summary>
        /// 全部链接下载分析完毕后触发
        /// </summary>
        public event DownloadFinishHandler DownloadFinish = null;
        #endregion

        #region public methods
        /// <summary>
        /// 开始下载
        /// </summary>
        /// <param name="path">保存本地文件的目录</param>
        public void Download(string path)
        {
            if (string.IsNullOrEmpty(RootUrl))
            {
                return;
            }
            _path = path;
            Init();
            StartDownload();
        }

        /// <summary>
        /// 终止下载
        /// </summary>
        public void Abort()
        {
            _stop = true;
            if (_workingSignals != null)
            {
                _workingSignals.AbortAllWork();
            }
        }
        #endregion

        #region 数据库操作
        //建立连接数据库的公共方法
        public static SqlConnection DBCon()
        {
            return new SqlConnection("server=home-pc;database=ASPTest;uid=sa;pwd=123456");
        }
        //插入操作
        public static void InsertData(string name, string description)
        {
            //string sql = "delete from dbo.API where apiName='name1'";
            //string sql = "insert into dbo.API (apiName,apiDescription) values('api2','description2')";
            string sql = "insert into dbo.API (apiName,apiDescription) values('" + name + "','" + description + "');";
            SqlConnection conn = DBCon();
            conn.Open();//打开数据库
            SqlCommand cmd = new SqlCommand(sql, conn);
            cmd.ExecuteNonQuery();
            Console.WriteLine("插入成功！");
            conn.Close();
        }

        #endregion
        #region private methods
        private void StartDownload()
        {
            _checkTimer = new Timer(new TimerCallback(CheckFinish), null, 0, 300);
            DispatchWork();
        }

        private void CheckFinish(object param)
        {
            if (_workingSignals.IsFinished())
            {
                _checkTimer.Dispose();
                _checkTimer = null;
                if (DownloadFinish != null)
                {
                    DownloadFinish(_index);
                }
            }
        }
        //每次一个工作实例完成工作，相应的_reqsBusy就设为false，并调用DispatchWork，给空闲的实例分配新任务了。
        private void DispatchWork()//请求资源。调度工作，控制并发的数量
        {
            if (_stop)//判断现在是否中止下载
            {
                return;
            }
            for (int i = 0; i < _reqCount; i++)//判断编号i的工作实例是否空闲，默认总共4个线程
            {
                if (!_reqsBusy[i])//非null时为忙碌
                {
                    RequestResource(i);//让此工作实例请求资源
                }
            }
        }

        private void Init()
        {
            _urlsLoaded.Clear();
            _urlsUnload.Clear();
            AddUrls(new string[1] { RootUrl }, 0);
            _index = 0;
            _reqsBusy = new bool[_reqCount];
            _workingSignals = new WorkingUnitCollection(_reqCount);
            _stop = false;
        }
        //发送请求
        private void RequestResource(int index)
        {
            int depth;
            string url = "";
            try
            {
                //C#提供了一个关键字lock，它可以把一段代码定义为互斥段，在一个时刻内只允许一个线程进入执行，而其他线程必须等待，对大括号内的函数有效。
                lock (_locker)//为了保证多个任务并发时的同步，加上了互斥锁。_locker是一个Object类型的成员变量
                {
                    //判断未下载集合是否为空，如果为空就把当前工作实例状态设为Finished；如果非空则设为Working并取出
                    //一个URL开始下载。当所有工作实例都为Finished的时候，说明下载已经完成。由于每次下载完一个URL后都
                    //调用DispatchWork，所以可能激活其他的Finished工作实例重新开始工作。
                    if (_urlsUnload.Count <= 0)//判断是否还有未下载的URL，如果都下载完成
                    {
                        _workingSignals.FinishWorking(index);//设置工作实例的状态为Finished
                        return;
                    }
                    _reqsBusy[index] = true;
                    _workingSignals.StartWorking(index);//设置工作状态为Working
                    depth = _urlsUnload.First().Value; //取出第一个未下载的URL
                    url = _urlsUnload.First().Key;
                    _urlsLoaded.Add(url, depth);//把该URL加入到已下载里
                    _urlsUnload.Remove(url);//把该URL从未下载中移除
                }
                //HttpWebRequest对象不是利用new关键字通过构造函数来创建的，而是利用工厂机制通过Create()方法来创建的。
                //Console.WriteLine(url);
                HttpWebRequest req = (HttpWebRequest)WebRequest.Create(url);
                req.Method = _method; //请求方法为get
                req.Accept = _accept; //接受的内容为text/html
                req.UserAgent = _userAgent; //用户代理
                //Console.WriteLine(url);
                RequestState rs = new RequestState(req, url, depth, index); //请求的额外信息在异步请求的回调方法作为参数传入
                var result = req.BeginGetResponse(new AsyncCallback(ReceivedResource), rs);//开始异步请求，这里需要传入
                //一个回调方法作为响应请求时的处理，同时传入回调方法的参数。
                ThreadPool.RegisterWaitForSingleObject(result.AsyncWaitHandle,
                        TimeoutCallback, rs, _maxTime, true);//给该异步请求注册一个超时处理方法TimeoutCallback，最大等待
                        //时间是_maxTime，且只处理一次超时，并传入请求的额外信息作为回调方法的参数。
            }
            catch (WebException we)
            {
                MessageBox.Show("RequestResource " + we.Message + url + we.Status);
            }
        }
        //请求的响应
        private void ReceivedResource(IAsyncResult ar)
        {
            RequestState rs = (RequestState)ar.AsyncState;//得到请求时传入的参数
            HttpWebRequest req = rs.Req;
            string url = rs.Url;
            try
            {
                HttpWebResponse res = (HttpWebResponse)req.EndGetResponse(ar);//获取响应
                if (_stop)//判断是否中止下载
                {
                    //Console.WriteLine("终止下载");
                    res.Close();
                    req.Abort();
                    return;
                }
                if (res != null && res.StatusCode == HttpStatusCode.OK)//判断是否成功获取响应
                {
                    Stream resStream = res.GetResponseStream();//得到资源流
                    rs.ResStream = resStream;
                    var result = resStream.BeginRead(rs.Data, 0, rs.BufferSize,//采用了异步的方法来读数据流是因为我们
                        new AsyncCallback(ReceivedData), rs);//之前采用了异步的方式请求，不然的话不能够正常的接收数据。
                    //该异步读取的方式是按包来读取的，所以一旦接收到一个包就会调用传入的回调方法ReceivedData，然后在该
                    //方法中处理收到的数据。该方法同时传入了接收数据的空间rs.Data和空间的大小rs.BufferSize。

                }
                else//响应失败
                {
                    res.Close();
                    rs.Req.Abort();
                    _reqsBusy[rs.Index] = false;//重置工作状态
                    DispatchWork();//分配新任务
                }
            }
            catch (WebException we)
            {
                MessageBox.Show("ReceivedResource " + we.Message + "------"+url+ "-------" + we.Status);
            }
            catch (Exception e)
            {
                MessageBox.Show(e.Message);
            }
        }

        private void ReceivedData(IAsyncResult ar)
        {
            RequestState rs = (RequestState)ar.AsyncState;//获取参数
            HttpWebRequest req = rs.Req;
            Stream resStream = rs.ResStream;
            string url = rs.Url;
            int depth = rs.Depth;
            string html = null;
            int index = rs.Index;
            int read = 0;

            try
            {
                read = resStream.EndRead(ar);//获得了读取的数据大小read，如果read>0说明数据可能还没有读完
                //如果read<=0说明所有数据已经接收完毕，这时rs.Html中存放了完整的HTML数据，就可以进行下一步的处理了。
                if (_stop)//判断是否中止下载
                {
                    rs.ResStream.Close();
                    req.Abort();
                    return;
                }
                if (read > 0)
                {
                    MemoryStream ms = new MemoryStream(rs.Data, 0, read);//利用获得的数据创建内存流
                    StreamReader reader = new StreamReader(ms, _encoding);
                    string str = reader.ReadToEnd(); //读取所有字符
                    rs.Html.Append(str);// 把这一次得到的字符串拼接在之前保存的字符串的后面，最后就能得到完整的HTML字符串。
                    var result = resStream.BeginRead(rs.Data, 0, rs.BufferSize,//再次异步请求读取数据，递归
                        new AsyncCallback(ReceivedData), rs);
                    return;
                }
                html = rs.Html.ToString();
                //匹配api名称
                MatchCollection matches = Regex.Matches(html, @"<h1[^>]*data-driver[^>]*api-title[^>]*>([^<]*)</h1>");
                //匹配api介绍
                MatchCollection matches1 = Regex.Matches(html, @"<p[^>]*class[^>]*description[^>]*>([^<]*)</p>");
                for (int i = 0; i < matches.Count; i++)
                {
                    InsertData(matches[i].Groups[1].Value.ToString(), matches1[i].Groups[1].Value.ToString());
                    //Console.WriteLine(matches[i].Groups[1].Value.ToString());
                    //Console.WriteLine(matches1[i].Groups[1].Value.ToString());
                }
                //SaveContents(html, url);//保存到本地
                string[] links = GetLinks(html);//获取页面中的链接
                AddUrls(links, depth + 1);//过滤链接并添加到未下载集合中
                _reqsBusy[index] = false;//重置工作状态
                DispatchWork();//分配新任务
            }
            catch (WebException we)
            {
                MessageBox.Show("ReceivedData Web " + we.Message + url + we.Status);
            }
            catch (Exception e)
            {
                MessageBox.Show(e.GetType().ToString() + e.Message);
            }
        }

        private void TimeoutCallback(object state, bool timedOut)
        {
            if (timedOut)//判断是否是超时
            {
                RequestState rs = state as RequestState;
                if (rs != null)
                {
                    rs.Req.Abort();//撤销请求
                }
                _reqsBusy[rs.Index] = false;//重置工作状态
                DispatchWork();//分配新任务
            }
        }

        private string[] GetLinks(string html)
        {
            const string pattern = "<h4 class=\"name\"><a href=.*?\">";
            Regex r = new Regex(pattern, RegexOptions.IgnoreCase);
            MatchCollection m = r.Matches(html);
            string[] links = new string[m.Count];

            for (int i = 0; i < m.Count; i++)
            {
                links[i] = m[i].ToString();
                links[i] = links[i].Substring(34);
                links[i] = links[i].Substring(0, links[i].Length - 1);
                links[i] = links[i].Substring(0, links[i].Length - 1);
                //Console.WriteLine(links[i]);
            }
            return links;
        }
        //判断链接是否已经下载或者已经处于未下载集合中
        private bool UrlExists(string url)
        {
            bool result = _urlsUnload.ContainsKey(url);
            result |= _urlsLoaded.ContainsKey(url);
            return result;
        }

        private bool UrlAvailable(string url)
        {
            if (UrlExists(url))
            {
                return false;//已经存在
            }
            if (url.Contains(".jpg") || url.Contains(".gif")
                || url.Contains(".png") || url.Contains(".css")
                || url.Contains(".js"))
            {
                return false;//去掉一些图片之类的资源
            }
            return true;
        }

        private void AddUrls(string[] urls, int depth)
        {
            if (depth >= _maxDepth)//深度过大
            {
                return;
            }
            foreach (string url in urls)
            {
                string cleanUrl = url.Trim();//去掉前后空格
                cleanUrl = cleanUrl.TrimEnd('/');//统一去掉最后面的'/'
                if (!cleanUrl.Contains("http://") && !cleanUrl.Contains("https://"))
                    cleanUrl = "http://" + cleanUrl;
                if (UrlAvailable(cleanUrl))
                {
                    _urlsUnload.Add(cleanUrl, depth);//是内链，直接加入未下载集合
                    //Console.WriteLine(cleanUrl);
                }
            }
        }

        //private void SaveContents(string html, string url)
        //{
        //    if (string.IsNullOrEmpty(html))
        //    {
        //        return;
        //    }
        //    string path = "";
        //    if (_index == 0)
        //    {
        //        lock (_locker)
        //        {

        //            path = string.Format("{0}\\{1}.txt", _path, _index++);
        //            Console.WriteLine(_index);
        //        }

        //        try
        //        {
        //            using (StreamWriter fs = new StreamWriter(path))
        //            {

        //                fs.Write(html);
        //            }

        //        }
        //        catch (IOException ioe)
        //        {
        //            MessageBox.Show("SaveContents IO" + ioe.Message + " path=" + path);
        //        }
        //    }
        //    else
        //    {
        //        _index++;
        //        //抽取name
        //        string pattern = "data-api-name=\".*?\"";
        //        Regex r = new Regex(pattern, RegexOptions.IgnoreCase);
        //        MatchCollection m = r.Matches(html);
        //        string[] name = new string[m.Count];

        //        for (int i = 0; i < m.Count; i++)
        //        {
        //            name[i] = m[i].ToString();
        //            name[i] = name[i].Substring(15);
        //            name[i] = name[i].Substring(0, name[i].Length - 1);
        //            Console.WriteLine(name[i]);
        //        }
        //        //抽取summary
        //        pattern = "<p data-driver=\"api-description\" class=\"description\">.*?<";
        //        r = new Regex(pattern, RegexOptions.IgnoreCase);
        //        m = r.Matches(html);
        //        string[] abstrct = new string[m.Count];

        //        for (int i = 0; i < m.Count; i++)
        //        {
        //            abstrct[i] = m[i].ToString();
        //            abstrct[i] = abstrct[i].Substring(54);

        //            abstrct[i] = abstrct[i].Substring(0, abstrct[i].Length - 1);
        //            Console.WriteLine(abstrct[i]);
        //        }
        //        //抽取图片
        //        pattern = "<div class=\"image-upload\"><img src=\"https://.*?\"";
        //        r = new Regex(pattern, RegexOptions.IgnoreCase);
        //        m = r.Matches(html);
        //        string[] pic = new string[m.Count];
        //        pic[0] = m[0].ToString();
        //        pic[0] = pic[0].Substring(44);
        //        pic[0] = pic[0].Substring(0, pic[0].Length - 1);
        //        //
        //        System.Uri uri = new Uri("http://"+pic[0]);
        //        Console.WriteLine(uri);
        //        //Get_img(uri);
        //        Console.WriteLine(_index);
        //            //写数据库
        //     }
        //    if (ContentsSaved != null)
        //    {
        //        ContentsSaved(path, url);
        //    }
        //}
        #endregion
        #region pic
        //private Bitmap Get_img(System.Uri httpUrl)
        //{
        //    Bitmap img = null;
        //    HttpWebRequest req;
        //    HttpWebResponse res = null;
        //    try
        //    {
        //        Console.WriteLine(httpUrl);
        //        req = (HttpWebRequest)(WebRequest.Create(httpUrl));
        //        req.Timeout = 180000; //设置超时值10秒
        //        req.UserAgent = "Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 6.1; Trident/4.0)";
        //        req.Accept = "image/*";
        //        req.Method = "GET";
        //        res = (HttpWebResponse)(req.GetResponse());
        //        img = new Bitmap(res.GetResponseStream());//获取图片流                 
        //        img.Save(@"E:/" + DateTime.Now.ToFileTime().ToString() + ".png");//随机名
        //    }

        //    catch (Exception ex)
        //    {
        //        string aa = ex.Message;
        //    }
        //    finally
        //    {
        //        res.Close();
        //    }
        //    return img;
        //}
        #endregion
    }
}
