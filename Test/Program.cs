using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Web;
using System.Net;
using System.IO;
using System.Text.RegularExpressions;

namespace Test
{
    class Program
    {
        static void Main(string[] args)
        {
            Dictionary<string, int> unload = new Dictionary<string, int>();
            Dictionary<string, int> loaded = new Dictionary<string, int>();

            unload.Add("https://news.sina.com.cn", 0);
            string baseUrl = "news.sina.com.cn";

            while (unload.Count > 0)
            {
                string url = unload.First().Key;
                int depth = unload.First().Value;
                loaded.Add(url, depth);
                unload.Remove(url);

                Console.WriteLine("Now loading " + url);

                HttpWebRequest req = (HttpWebRequest)WebRequest.Create(url);
                req.Method = "GET";
                req.Accept = "text/html";
                req.UserAgent = "Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 6.1; Trident/4.0)";

                try
                {
                    string html = null;
                    HttpWebResponse res = (HttpWebResponse)req.GetResponse();
                    using (StreamReader reader = new StreamReader(res.GetResponseStream()))
                    {
                        html = reader.ReadToEnd();
                        if (!string.IsNullOrEmpty(html))
                        {
                            Console.WriteLine("Download OK!\n");
                        }
                    }
                    string[] links = GetLinks(html);
                    AddUrls(links, depth + 1, baseUrl, unload, loaded);
                }
                catch (WebException we)
                {
                    Console.WriteLine(we.Message);
                }
            }
        }

        private static string[] GetLinks(string html)
        {
            const string pattern = @"http://([\w-]+\.)+[\w-]+(/[\w- ./?%&=]*)?";
            Regex r = new Regex(pattern, RegexOptions.IgnoreCase);
            MatchCollection m = r.Matches(html);
            string[] links = new string[m.Count];

            for (int i = 0; i < m.Count; i++)
            {
                links[i] = m[i].ToString();
            }
            return links;
        }

        private static bool UrlAvailable(string url, Dictionary<string, int> unload, Dictionary<string, int> loaded)
        {
            if (unload.ContainsKey(url) || loaded.ContainsKey(url))
            {
                return false;
            }
            if (url.Contains(".jpg") || url.Contains(".gif")
                || url.Contains(".png") || url.Contains(".css")
                || url.Contains(".js"))
            {
                return false;
            }
            return true;
        }

        private static void AddUrls(string[] urls, int depth, string baseUrl, Dictionary<string, int> unload, Dictionary<string, int> loaded)
        {
            if (depth >= 3)
            {
                return;
            }
            foreach (string url in urls)
            {
                string cleanUrl = url.Trim();
                int end = cleanUrl.IndexOf(' ');
                if (end > 0)
                {
                    cleanUrl = cleanUrl.Substring(0, end);
                }
                if (UrlAvailable(cleanUrl, unload, loaded))
                {
                    if (cleanUrl.Contains(baseUrl))
                    {
                        unload.Add(cleanUrl, depth);
                    }
                    else
                    {
                        // 外链
                    }
                }
            }
        }
    }
}
