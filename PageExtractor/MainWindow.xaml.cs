using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Documents;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Media.Imaging;
using System.Windows.Navigation;
using System.Windows.Shapes;
using System.Threading;

namespace PageExtractor
{
    /// <summary>
    /// MainWindow.xaml 的交互逻辑
    /// </summary>
    public partial class MainWindow : Window
    {
        private Spider _spider = null;
        private delegate void CSHandler(string arg0, string arg1);
        private delegate void DFHandler(int arg1);

        public MainWindow()
        {
            InitializeComponent();
            _spider = new Spider();
            _spider.ContentsSaved += new Spider.ContentsSavedHandler(Spider_ContentsSaved);
            _spider.DownloadFinish += new Spider.DownloadFinishHandler(Spider_DownloadFinish);
            this.Closed += new EventHandler(MainWindow_Closed);
            this.Loaded += new RoutedEventHandler(MainWindow_Loaded);
            btnStop.IsEnabled = false;
        }

        void MainWindow_Loaded(object sender, RoutedEventArgs e)
        {
            TextUrl.Text = "news.sina.com.cn";
        }
        
        void Spider_DownloadFinish(int count)
        {
            DFHandler h = c =>
            {
                _spider.Abort();
                btnDownload.IsEnabled = true;
                btnDownload.Content = "Download";
                btnStop.IsEnabled = false;
                MessageBox.Show("Finished " + c.ToString());
            };
            Dispatcher.Invoke(h, count);
        }

        void MainWindow_Closed(object sender, EventArgs e)
        {
            _spider.Abort();
        }

        private void btnDownload_Click(object sender, RoutedEventArgs e)
        {
            _spider.RootUrl = TextUrl.Text;
            Thread thread = new Thread(new ParameterizedThreadStart(Download));
            thread.Start(TextPath.Text);
            btnDownload.IsEnabled = false;
            btnDownload.Content = "Downloading...";
            btnStop.IsEnabled = true;
        }

        private void Download(object param)
        {
            _spider.Download((string)param);
        }

        void Spider_ContentsSaved(string path, string url)
        {
            CSHandler h = (p, u) =>
            {
                ListDownload.Items.Add(new { Url = u, File = p });
            };
            Dispatcher.Invoke(h, path, url);
        }

        private void btnStop_Click(object sender, RoutedEventArgs e)
        {
            _spider.Abort();
            btnDownload.IsEnabled = true;
            btnDownload.Content = "Download";
            btnStop.IsEnabled = false;
        }

        private void FolderButton_Click(object sender, RoutedEventArgs e)
        {
            System.Windows.Forms.FolderBrowserDialog fdlg = new System.Windows.Forms.FolderBrowserDialog();
            fdlg.RootFolder = Environment.SpecialFolder.Desktop;
            fdlg.Description = "Contents Root Folder";
            var result = fdlg.ShowDialog();
            if (result == System.Windows.Forms.DialogResult.OK)
            {
                string path = fdlg.SelectedPath;
                TextPath.Text = path;
            }
        }

        private void PropertyButton_Click(object sender, RoutedEventArgs e)
        {
            PropertyWindow pw = new PropertyWindow()
            {
                MaxDepth = _spider.MaxDepth,
                MaxConnection = _spider.MaxConnection,
                WindowStartupLocation = System.Windows.WindowStartupLocation.CenterScreen
            };
            if (pw.ShowDialog() == true)
            {
                _spider.MaxDepth = pw.MaxDepth;
                _spider.MaxConnection = pw.MaxConnection;
            }
        }
    }
}
